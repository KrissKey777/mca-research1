# INTEGRATION RECORDS — the strongest theorems of the package

Ten dokument to *paczka integracyjna*: dla każdego najsilniejszego twierdzenia repozytorium
jeden krótki rekord w ustalonym formacie, plus rola (`RIGIDITY`, `STRICT_DESCENT`,
`FINITE_CHALLENGE_COST`, `META-BARRIER`).  Matematyka **nie** została przeorganizowana pod
istniejący DAG: każdy wpis podaje twierdzenie w jego naturalnej, najmocniejszej formie, dokładnie
tak jak stoi w źródłach Lean.  Integracja (składanie w łańcuchy) jest zostawiona na później; tu
podane są tylko dane potrzebne do jej wykonania.

Nothing in this file is new mathematics and no Lean file was changed while writing it: every
record is a transcription of a declaration that is already in the sources, with the fields the
integration step needs.  Line numbers are omitted deliberately (they move); the declaration name
and file are the stable key.

---

## 0. Legend and conventions

Notation: `n = |D|` (block length), `k` = dimension (degree bound), `e` = radius,
`ρ = k/n`, `δ = e/n`, `q = |F|`, `#Bad = (badSet k e f₀ f₁).card`, `Λ` a list size.
"Line" = the received pair `(f₀, f₁)` together with the challenge family `γ ↦ f₀ + γ·f₁`.

**OFFICIAL SAME-SUPPORT.**  The repository's official badness predicate is

```
IsBad k e f₀ f₁ γ  :=  ∃ S : Finset ↥D,  n ≤ |S| + e  ∧  IsCloseOn k S (f₀ + γ·f₁)
                                        ∧  ¬ LineCloseOn k S f₀ f₁      (RequestProject/Root/CodingTheory/MCA.lean)
```

i.e. the *same* set `S` must explain the whole line, not merely each point separately; the
alphabet form (`AlphabetMCA.IsBad`) and the arity-`ℓ` generator form (`PolyGen.IsBadG`) carry the
identical quantifier.  `Root.CodingTheory.GG25Literal.strongMCA_iff_GG25MCA` proves this notion
equivalent to the literature definition (record R2).  A record answers **YES** to
*OFFICIAL SAME-SUPPORT PRESERVED?* exactly when its statement is phrased in `IsBad`/`badSet`
(or `IsBadG`/`badSetG`, or `Alphabet.badSet`) and **NO** when it is phrased in the
proximity-only surrogate `goodZ` / `distToCode` (which asks only that the individual point
`f₀ + γ·f₁` be close, forgetting the common support).

**UNIFORM OVER ALL RECEIVED PAIRS?**  YES = the statement quantifies over *all* pairs
`(f₀, f₁) : (↥D → F)²` with no structural condition on the words (window conditions on
`n, k, e` are allowed, and are listed under EXACT HYPOTHESES).  NO = the pair is constrained
(far centre, rigid/localised family, orbit-spanned words, or one explicit pencil), or the
statement is an existence/counterexample statement about one particular pair.

**PROOF STATUS.**  `Lean` means: machine-checked in this repository and `sorry`-free.  Every
declaration named in this file was re-checked while the file was written: each one elaborates
under its stated name, and `#print axioms` on it reports only `propext`, `Classical.choice`,
`Quot.sound` (`FFT.fftMulsOpt_eq` uses only `propext`, `Quot.sound`).  The repository's standing
audits live in `RequestProject/Main.lean` and in the dedicated files
`RequestProject/*AxiomAudit.lean`.  The whole project builds clean (8348 jobs, 0 errors).  No record in this file is conditional or heuristic; where a *hypothesis* is
conjectural (e.g. a supplied list-size bound) that is stated explicitly in EXACT HYPOTHESES, and
the theorem itself is still a Lean theorem about that hypothesis.

**ROLES.**

* `RIGIDITY` — the theorem's content is a dichotomy or an exact structural characterisation:
  either a cheap bound holds, or the received data are forced into a rigid/degenerate shape.
* `STRICT_DESCENT` — the theorem replaces the instance by a smaller one along an explicit
  measure (deletion depth, corank, arity, support size, coordinate count), and that measure
  strictly decreases.
* `FINITE_CHALLENGE_COST` — the theorem bounds the number of bad challenges (or `ε_mca`, or an
  arithmetic operation count) by an explicit finite quantity.
* `META-BARRIER` — the theorem is negative: it shows a route, hypothesis, or conjectured
  scaling cannot work, or exhibits a lower bound that no method of the given shape can beat.

---

## 1. Foundational / official-definition records

### R1 — Correlated agreement from acceptance probability (the root witness)

* **DECLARATION:** `Root.CodingTheory.correlatedAgreement_of_prob_gt` — `RequestProject/Root/CodingTheory/MCA.lean`
* **EXACT HYPOTHESES:** `F` a finite field, `D : Finset F`; section variables `1 ≤ k`,
  `k ≤ n`, `3e < n − k + 1`; and `n/q < Pr_{γ ← F}[distToCode k (f₀ + γ·f₁) ≤ e]`.
* **EXACT CONCLUSION:** `∃ S : Finset ↥D, n ≤ |S| + e ∧ LineCloseOn k S f₀ f₁` — one common
  agreement set of size `≥ n − e` for *every* point of the line.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — the conclusion *is* the same-support statement
  (`LineCloseOn`), and the hypothesis is the raw acceptance probability.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES — `f₀ f₁` are arbitrary.
* **QUANTITATIVE COST / CARDINAL BOUND:** error term `n/q`; equivalently `#Bad ≤ n` in this
  window (`card_badSet_le`).
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The identity of the bad challenges and the number
  of distinct common supports: only existence of one `S` is delivered.
* **SHARPNESS / BARRIER THEOREM:** `Root.CodingTheory.card_le_epsMCAmax_of_blocks` (R36) gives
  `ε_mca ≥ r/q`, so an error term of order `1/q` is unavoidable; the `3e` window is optimal by
  R5.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R2 — The project's MCA is literally the literature's MCA

* **DECLARATION:** `Root.CodingTheory.GG25Literal.strongMCA_iff_GG25MCA` — `RequestProject/Root/CodingTheory/GG25LiteralMCA.lean`
* **EXACT HYPOTHESES:** `C : Submodule F (ι → A)` a linear code over a finite field with a
  finite index type, `0 < Fintype.card ι`; rational parameters `δ err`.
* **EXACT CONCLUSION:** `StrongMCA C δ err ↔ GG25MutualCorrelatedAgreement C δ err`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — this is the theorem that *certifies* the
  same-support convention: both sides quantify one common agreement set.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES — both predicates quantify over all pairs `(u₀,u₁)`.
* **QUANTITATIVE COST / CARDINAL BOUND:** none (an equivalence, cost 0); it makes the exact
  conversion `#Bad ≤ B ⇒ ε_mca ≤ B/q` legitimate against the literature statement.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing — it is an iff.
* **SHARPNESS / BARRIER THEOREM:** it is itself the barrier: the project's definition is *not*
  strictly stronger, so any constant gap to the literature is a gap of proofs, not definitions.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

---

## 2. Finite challenge cost — unconditional and window bounds

### R3 — The unconditional subresultant bound `#Bad ≤ (k+1)e + 1`

* **DECLARATION:** `Root.CodingTheory.Subresultant.card_badSet_le_unconditional` — `RequestProject/Root/CodingTheory/SubresultantCorrelatedBridge.lean`
* **EXACT HYPOTHESES:** `F` a finite field, `D : Finset F`, `1 ≤ k`, `k + 2e ≤ n`.  No
  hypothesis whatsoever on `(f₀, f₁)`.
* **EXACT CONCLUSION:** `(badSet k e f₀ f₁).card ≤ (k + 1) * e + 1`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** `(k+1)e + 1 = O(k·e)`, i.e. `O(n²)` at constant rate
  and radius; `ε_mca ≤ ((k+1)e+1)/q`.
* **STRICTLY DECREASING DESCENT MEASURE:** none (a degree count of the Welch–Berlekamp/
  subresultant pencil, not a descent).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The witnesses: the bound counts roots of a
  determinant, so the common support `S` attached to each bad challenge is discarded.
* **SHARPNESS / BARRIER THEOREM:** the window `k + 2e ≤ n` is exactly where forcing is unique
  (R32); beyond it the mechanism has no output.  Inside the window,
  `Root.CodingTheory.not_forall_card_badSet_le_succ_radius_of_strict_ud`
  (`UniqueDecodingHoleWitness.lean`) exhibits a line with `#Bad = e + 2`, so a bound of the form
  `e + 1` is impossible here; whether the factor `k` is needed is open.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R4 — The sharp unique-decoding count `#Bad ≤ e + 1`

* **DECLARATION:** `Root.CodingTheory.card_badSet_le_succ_radius` — `RequestProject/Root/CodingTheory/UniqueDecodingMCA.lean`
* **EXACT HYPOTHESES:** finite field; section variables `1 ≤ k`, `k ≤ n`, `3e < n − k + 1`
  (i.e. `δ < (1−ρ)/3` up to rounding).  Arbitrary `f₀ f₁`.
* **EXACT CONCLUSION:** `(badSet k e f₀ f₁).card ≤ e + 1`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** `e + 1`; `ε_mca ≤ (e+1)/q`.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The witnesses again; only the cardinality survives.
* **SHARPNESS / BARRIER THEOREM:** `Root.CodingTheory.not_forall_card_badSet_le_one`
  (the value `e+1` cannot be lowered) and R5 (the hypothesis `3e` cannot be relaxed to `2e`).
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R5 — The `3e` window of R4 is optimal (`2e` fails, `#Bad = n`)

* **DECLARATION:** `Root.CodingTheory.not_forall_card_badSet_le_succ_radius_of_two_radius` — `RequestProject/Root/CodingTheory/UniqueDecodingGapWitness.lean`
* **EXACT HYPOTHESES:** none (a closed refutation over `ZMod 5`).
* **EXACT CONCLUSION:** `¬ ∀ (D : Finset (ZMod 5)) (k e) (f₀ f₁), 1 ≤ k → k ≤ n →
  2e < n − k + 1 → (badSet k e f₀ f₁).card ≤ e + 1`; the explicit counterexample has
  `D = {0,1,2,3}`, `k = 2`, `e = 1` and four bad challenges.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — the four challenges are bad in the official sense.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — one explicit pair (as required of a counterexample).
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad = 4 = n` at `e = 1`.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing; a finite decidable certificate.
* **SHARPNESS / BARRIER THEOREM:** this *is* the sharpness statement for R4.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R6 — The arity-`ℓ` sharp bound `#Bad ≤ (ℓ−1)(e+1)`

* **DECLARATION:** `Root.CodingTheory.PolyGen.card_badSetG_le_sharp` — `RequestProject/Root/CodingTheory/PolynomialGeneratorMCA.lean`
* **EXACT HYPOTHESES:** finite field; `1 ≤ k`, `k + (ℓ+1)e ≤ n`; arbitrary family
  `f : ℕ → ↥D → F` (only the first `ℓ` words matter).
* **EXACT CONCLUSION:** `(badSetG l k e f).card ≤ (l − 1) * (e + 1)`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — `badSetG` uses the common-support quantifier
  `GenCloseOn` for the whole generated family.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES (all families of arity `ℓ`; `ℓ = 2` is the line case).
* **QUANTITATIVE COST / CARDINAL BOUND:** `(ℓ−1)(e+1)`, independent of `n` and `q`.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The witnesses and the position of the bad
  challenges inside `F`.
* **SHARPNESS / BARRIER THEOREM:** `Root.CodingTheory.PolyGen.exists_card_badSetG_eq_sharp`:
  in the same window, over a field with `(e+1)(ℓ−1) ≤ q`, the maximum of `#Bad` over all
  families is *exactly* `(ℓ−1)(e+1)`.  The window `k + (ℓ+1)e ≤ n` forces `δ ≤ (1−ρ)/3` at
  `ℓ = 2`.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R7 — The window-free circuit-incidence bound (no field size, no separation window)

* **DECLARATION:** `Root.CodingTheory.PolyGen.card_badSetG_le_circuit` — `RequestProject/Root/CodingTheory/GeneratorCircuitIncidence.lean`
* **EXACT HYPOTHESES:** finite field; `T = max (n − e) (k+1)` and any test size `a` with
  `k + 1 ≤ a ≤ T`.  No condition relating `k`, `e`, `n`; arbitrary family `f`.
* **EXACT CONCLUSION:** `(badSetG l k e f).card * (T − 1).choose (a − 1) ≤ n.choose a * (l − 1)`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≤ (ℓ−1)·C(n,a)/C(T−1,a−1)`; the field size `q`
  never appears, so on sparse domains `#Bad < q` and `ε_mca → 0`.
* **STRICTLY DECREASING DESCENT MEASURE:** none (an incidence/double count over `a`-subsets).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Which coordinate subset certifies which
  challenge; the bound only counts incidences.
* **SHARPNESS / BARRIER THEOREM:** `Root.CodingTheory.PolyGen.Saturation.card_badSetG_satFam_zmod_ge`
  (R32) shows a family with `p − 1` bad challenges out of `p`, so for dense domains the bound
  is vacuous — its content is the *sparse* regime (`SparseDomainSharpness.lean` gives matching
  small cases).
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R8 — The pair-covering composition with a free threshold `τ`

* **DECLARATION:** `Root.CodingTheory.card_badSet_le_pairCover` — `RequestProject/Root/CodingTheory/MCAPairCover.lean`
* **EXACT HYPOTHESES:** finite field; a threshold `τ` with `n·(τ−1) < (n−e)²` (this inequality
  is exactly the Johnson-type condition `δ < 1 − √ρ` when `τ = k`).  Arbitrary `f₀ f₁`.
* **EXACT CONCLUSION:**
  `#Bad ≤ n·Λ(k,τ)² + n(n−e)/((n−e)² − n(τ−1))` over `ℝ`, with `Λ = listSizeMax D k τ`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** structured layer `n·Λ²`, residual layer
  `O(n(n−e)/((n−e)²−n(τ−1)))`; with the Guruswami–Sudan list size substituted
  (`epsMCAmax_le_pairCover_gs`) it becomes an explicit `ε_mca` bound.
* **STRICTLY DECREASING DESCENT MEASURE:** none, but `τ` is a free parameter that trades the two
  layers against each other — the integration knob of this record.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The bad set is split into "explained by a codeword
  pair" and "isolated"; inside the structured bucket the individual challenge is replaced by its
  pair, and inside the residual bucket by an intersection count.
* **SHARPNESS / BARRIER THEOREM:** the residual layer needs `n(τ−1) < (n−e)²`; the structured
  layer pays `Λ(k,τ)²`, which is not polynomial below the Johnson agreement threshold `√(nk)`
  — that unmeasured layer is where the spine stops.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R9 — The set-family Johnson bound (the counting engine of R8 and R26)

* **DECLARATION:** `Root.CodingTheory.card_family_le_of_pairwise_inter` — `RequestProject/Root/CodingTheory/SetFamilyJohnson.lean`
* **EXACT HYPOTHESES:** a finite ambient type `α`, an index set `A`, sets `S i` with
  `t ≤ |S i|` for `i ∈ A`, and `|S i ∩ S j| ≤ c` for distinct `i, j ∈ A`.
* **EXACT CONCLUSION:** `|A| · (t² − |α|·c) ≤ |α| · t` over `ℝ`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a — pure combinatorics, no code and no challenge; it is
  applied to same-support witnesses without weakening them.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES (it is pair-free).
* **QUANTITATIVE COST / CARDINAL BOUND:** `|A| ≤ |α|t/(t² − |α|c)` when `t² > |α|c`.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** All algebra: only sizes and pairwise meets remain.
* **SHARPNESS / BARRIER THEOREM:** the side condition `t² > |α|c` is exactly `δ < 1 − √ρ` in the
  MCA application, i.e. the Johnson wall is built into the engine.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R10 — A `#Bad ≤ 1` certificate for folded Reed–Solomon

* **DECLARATION:** `Root.CodingTheory.foldedRS_card_badSet_le_one` — `RequestProject/Root/CodingTheory/ZeroLocusGeneral.lean`
* **EXACT HYPOTHESES:** finite field; folding data `0 < s`, `IsFoldingDomain B s γ`, degree
  bounds `k ≤ k'`, `(k'−1)/s < |B|`, `(k'−1)/s < t`, radius condition `2e + t ≤ |B|`; and the
  structural condition on the received pair: `f₁ ∉ foldedRSCode B k s γ` but
  `f₁ ∈ foldedRSCode B k' s γ` (the direction word is a codeword of the *ambient* folded code
  but not of the tested one).
* **EXACT CONCLUSION:** `(Alphabet.badSet (foldedRSCode B k s γ) e f₀ f₁).card ≤ 1`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — `Alphabet.badSet` is the same-support predicate for
  a general linear code over an alphabet.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — the direction word `f₁` is constrained as above
  (`f₀` is arbitrary).
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≤ 1`, hence `ε_mca ≤ 1/q` — the smallest
  possible nontrivial constant.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing beyond the cardinality; but the
  hypothesis restricts the class of instances, which is where the strength is bought.
* **SHARPNESS / BARRIER THEOREM:** `#Bad ≥ 1` is attainable, so `1` is optimal;
  `GENERALITY_CHECKPOINT.md` records that the hypothesis on `f₁` is the whole content — for
  arbitrary `f₁` the bound is false (see R30/R31 for exponential bad sets).
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R11 — Far-centred triple-cluster proximity: `#Bad = O(n)` below `δ = 1 − ρ^{1/3}`

* **DECLARATION:** `Root.CodingTheory.card_badSet_le_of_far_of_rate_radius` — `RequestProject/Root/CodingTheory/TripleClusterProximity.lean`
* **EXACT HYPOTHESES:** finite field; `1 ≤ k ≤ n`, `10k ≤ 3n`, `10e ≤ 3n`, `25c ≤ n`, and the
  centre is far: `e < distToCode k f₀`.
* **EXACT CONCLUSION:** `(badSet k e f₀ f₁).card * c ≤ (e + 2) * n`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — only far centres (`distToCode k f₀ > e`); the
  near-centre case is the complementary branch and is not covered here.
* **QUANTITATIVE COST / CARDINAL BOUND:** with `c = ⌊n/25⌋`, `#Bad ≤ 25(e+2)`, i.e. `O(n)`, so
  `ε_mca = O(n/q)`, at rate and radius up to `3/10` — past `(1−ρ)/3 = 7/30` at `ρ = 3/10`.
* **STRICTLY DECREASING DESCENT MEASURE:** none; the mechanism is an energy count over triples.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The witnesses, and the distinction between the
  clusters: the conclusion is a single cardinality.
* **SHARPNESS / BARRIER THEOREM:** the far-centre hypothesis is essential (a near centre gives
  the whole unique-decoding picture instead); `regime_example_1000_251_300` in the same file
  exhibits a parameter point inside this regime and outside the `3e` window of R4.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R12 — The Frobenius-orbit budget: `#Bad ≤ 1 + q₀ + ⋯ + q₀^{d−1}`

* **DECLARATION:** `Root.CodingTheory.card_badSet_mul_le_of_orbit` — `RequestProject/Root/CodingTheory/FrobeniusOrbitBudget.lean`
* **EXACT HYPOTHESES:** finite field; a ring endomorphism `σ : F →+* F` of order `m > 0`
  (`σ^m = id`, the `m` iterates pairwise distinct as monoid homs) fixing `D` pointwise;
  `σ`-fixed words `u : Fin d → (↥D → F)`, scalars `a b : Fin d → F` with `f₀ = Σ aⱼuⱼ`,
  `f₁ = Σ bⱼuⱼ`, and minimality: no nonzero `σ`-fixed covector annihilates both `a` and `b`.
* **EXACT CONCLUSION:** `#Bad · (q₀ − 1) + 1 ≤ q₀^d`, where `q₀ = |Fix σ|`; equivalently
  `#Bad ≤ 1 + q₀ + ⋯ + q₀^{d−1}`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — the pair must lie in the span of `d` Frobenius-fixed
  words (the Galois-structured class), with the minimality condition.
* **QUANTITATIVE COST / CARDINAL BOUND:** the projective count `(q₀^d − 1)/(q₀ − 1)`; at `d = 2`
  this is `q₀ + 1` challenges, i.e. Galois-type constraint-rank compression is capped at `p + 1`
  for a prime base field.
* **STRICTLY DECREASING DESCENT MEASURE:** the orbit dimension `d` — each descent step of the
  chain lowers `d`, and the budget is monotone in it.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The individual challenge is replaced by a
  rational direction in the `σ`-fixed covector space; distinct challenges with the same
  direction are not separated.
* **SHARPNESS / BARRIER THEOREM:** `OrbitThreeSharpness.lean` (the `d = 3` relation is sharp) and
  R20/R21: at `d = 3` a bad set above the budget forces genuine list-decoding ambiguity, and on
  the deployed KoalaBear row the cap sits 27 bits below the Prize threshold.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R13 — The affine-carrier budget (the closed branch of the irreducible-carrier route)

* **DECLARATION:** `Root.CodingTheory.CarrierBudget.card_badSet_le_of_affine_carriers_sharp` — `RequestProject/Root/CodingTheory/CarrierBudget.lean`
* **EXACT HYPOTHESES:** finite field; a far centre `e + 1 < distToCode k f₀`; a nonzero
  trivariate `Q` with `Q.natDegree ≤ L` and all `Z`-degrees `≤ dZ`; every close challenge is
  witnessed by a root of `Q` agreeing off `e` positions (`hroot`); and every degenerate
  irreducible factor of `Q` with a large line support is an affine carrier (`haffine`).
* **EXACT CONCLUSION:** `(badSet k e f₀ f₁).card ≤ dZ + n * (dZ + L)`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — far centre plus the interpolant hypotheses on `Q`.
* **QUANTITATIVE COST / CARDINAL BOUND:** `dZ + n(dZ + L)`, i.e. linear in `n` once the
  interpolant degrees are constant.
* **STRICTLY DECREASING DESCENT MEASURE:** the factorisation of `Q`: each irreducible carrier
  peeled off strictly lowers `natDegree Q`.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Which factor explains which challenge; also the
  non-degenerate factors are charged wholesale by their degree.
* **SHARPNESS / BARRIER THEOREM:** the companion dichotomy
  `CarrierBudget.card_le_or_exists_degenerate_irreducible_sharp` is sharp, and
  `DeployedTargetGap.lean` measures the residual gap to the deployed target — this branch alone
  does not reach it.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

---

## 3. Rigidity records (dichotomies and exact characterisations)

### R14 — The rigidity dichotomy for the arity-`ℓ` syndrome family

* **DECLARATION:** `Root.CodingTheory.PolyGen.Hankel.card_le_or_rigid` — `RequestProject/Root/CodingTheory/SyndromeRigidityDichotomy.lean`
* **EXACT HYPOTHESES:** finite field; a set `B` of challenges with `B ⊆ badSetG l k e f`, the
  moment window `e·|B| + k ≤ n`, and `l ≤ |B|`.
* **EXACT CONCLUSION:** `|B| ≤ (e+1)(l−1) ∨ RigidOn l k e f`, where
  `RigidOn l k e f := ∃ T, |T| ≤ e ∧ ∀ j < l, IsCloseOn k Tᶜ (f j)` — *all* generators are
  explained off one and the same set of at most `e` positions.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — `badSetG` on the left, and the rigid branch is
  itself a same-support statement (one `T` for all words).
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES — no non-degeneracy hypothesis on `f`.
* **QUANTITATIVE COST / CARDINAL BOUND:** `(e+1)(ℓ−1)` on the cheap branch; the rigid branch
  carries no cardinality but hands over a set `T` with `|T| ≤ e`.
* **STRICTLY DECREASING DESCENT MEASURE:** on the rigid branch the instance descends to the
  shortened instance on `Tᶜ`; the measure is `n − |T| ≥ n − e`, strictly below `n`.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** On the cheap branch, the witnesses; on the rigid
  branch, the individual challenges — one learns only that a common error support exists.
* **SHARPNESS / BARRIER THEOREM:** the constant `(e+1)(ℓ−1)` is exactly the sharp value of R6,
  attained; the window `e·|B| + k ≤ n` is quadratic in `|B|` and is what R15 removes to a linear
  one at the price of a weaker degenerate branch.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

### R15 — Support concentration: the degenerate branch is geometric, not determinantal

* **DECLARATION:** `Root.CodingTheory.PolyGen.Hankel.card_le_or_support_le` — `RequestProject/Root/CodingTheory/SyndromeSupportPhase.lean`
* **EXACT HYPOTHESES:** finite field; `B ⊆ badSetG l k e f` and the window `e·|B| + k ≤ n`.
  No non-degeneracy, no `l ≤ |B|`.
* **EXACT CONCLUSION:** `|B| ≤ (e+1)(l−1) ∨ ∃ T, |T| ≤ e ∧ ∀ γ ∈ B, IsCloseOn k Tᶜ (genComb l f γ)`
  — either the cheap count, or *every challenged word of `B`* is explained off one common set of
  at most `e` positions.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** `(e+1)(ℓ−1)`.
* **STRICTLY DECREASING DESCENT MEASURE:** as in R14, the surviving coordinate set `Tᶜ`
  (`|T| ≤ e`).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The determinantal certificate: this version
  deliberately forgets the vanishing minors and keeps only the error geometry.
* **SHARPNESS / BARRIER THEOREM:** `SupportPhaseSharpness.lean` (the support-concentration law is
  attained); and the window `e·|B| + k ≤ n` cannot be dropped — the saturating family R32 sits
  just outside it (`satFam_outside_window`: `k + (ℓ+1)e = |F| + 1 > |D|`) and has `#Bad ≥ q − 1`.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

### R16 — The exact kernel law of the syndrome Hankel system

* **DECLARATION:** `Root.CodingTheory.hankelRel_iff_locator_mul` — `RequestProject/Root/CodingTheory/HankelLocatorKernel.lean`
* **EXACT HYPOTHESES:** a field; an error set `E`, nonvanishing amplitudes `a` on `E`, column
  count `cols`, row count `rows` with `|E| ≤ rows`, and `deg L < cols`.
* **EXACT CONCLUSION:** `HankelRel (momentSeq E a) cols rows L ↔ ∃ G, L = supportLocator E * G ∧
  deg G < cols − |E|` — the kernel is exactly `Λ_E · F[X]_{< cols−|E|}`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a — a statement about the moment/Hankel system, not
  about `IsBad`; it is used to certify that a kernel vector is a genuine locator.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES for every error configuration with `|E| ≤ rows`.
* **QUANTITATIVE COST / CARDINAL BOUND:** kernel dimension exactly `cols − |E|`.
* **STRICTLY DECREASING DESCENT MEASURE:** the defect `cols − 1 − |E|`.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing — it is an exact characterisation (iff).
* **SHARPNESS / BARRIER THEOREM:** `exists_hankelRel_nonvanishing` in the same file: as soon as
  `rows < |E| ≤ cols` there is a kernel vector vanishing nowhere on `E`, so the hypothesis
  `|E| ≤ rows` is exactly the boundary of the law, and locator repair fails past it.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

### R17 — Bad = vanishing syndrome determinant, exactly, in the minimal-support phase

* **DECLARATION:** `Root.CodingTheory.PolyGen.mem_badSetG_iff_det_syndromeMatrix_eq_zero` — `RequestProject/Root/CodingTheory/MinimalSupportHankelBridge.lean`
* **EXACT HYPOTHESES:** finite field; codewords `q j` of degree `< k`; `l ≤ |F|`; window
  `k + 2e + 1 ≤ n`; and the phase condition `|jointSupport l f q| = e + 1` (minimal support).
* **EXACT CONCLUSION:** `γ ∈ badSetG l k e f ↔ (syndromeMatrix l e f q γ).det = 0`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — the left-hand side is the official bad set.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — only families in the `M = e+1` minimal-support phase.
* **QUANTITATIVE COST / CARDINAL BOUND:** through the degree of the determinant this gives
  `#Bad ≤ e + 1` in the phase; the point of the record is that the locus is *exact*, not merely
  contained.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing inside the phase (iff); outside the phase
  the statement says nothing.
* **SHARPNESS / BARRIER THEOREM:** `MinimalSupportExtremalPhase.lean` classifies the phase
  completely and shows the exclusion route ends there; R35 shows the subresultant description
  is void on the same locus.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

### R18 — The Johnson-radius structural dichotomy (unconditional)

* **DECLARATION:** `Root.CodingTheory.johnson_escape_or_structure` — `RequestProject/Root/CodingTheory/JohnsonStructuralDichotomy.lean`
* **EXACT HYPOTHESES:** finite field; `t + e = n`; any threshold `c`.  Arbitrary `f₀ f₁`.
* **EXACT CONCLUSION:** either **ESCAPE** `#Bad·(t² − n·c) ≤ n·t` (over `ℝ`), or **STRUCTURE**
  there are codewords `q₀, q₁` of degree `< k` with `|pairAgreement f₀ f₁ q₀ q₁| ≥ c + 1`
  explaining two distinct bad challenges.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — both branches are about `badSet`, and the structure
  branch produces one codeword pair with a *common* agreement set.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES — no hypothesis on the words at all.
* **QUANTITATIVE COST / CARDINAL BOUND:** at `c = k`, ESCAPE gives `#Bad ≤ nt/(t² − nk)`,
  informative exactly when `nk < t²`, i.e. `δ < 1 − √ρ`.
* **STRICTLY DECREASING DESCENT MEASURE:** none; but the structure branch produces a *single*
  pair, which is the input for pair-fibre bounds (`card_badPairSet_le`, fibre `≤ n`).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** In the ESCAPE branch, the algebra (only sizes of
  witness sets remain); in the STRUCTURE branch, all challenges other than the two produced.
* **SHARPNESS / BARRIER THEOREM:** `escape_rho_half_delta_gt_quarter` and
  `johnson_rho_half_delta_quarter` in the same file pin the deployed row `n = 2²⁰`, `ρ = 1/2`:
  the dichotomy is informative up to the Johnson radius and no further.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

### R19 — The `d = 3` Frobenius-orbit dichotomy: excess badness forces ambiguity

* **DECLARATION:** `Root.CodingTheory.card_badSet_le_ambiguity` — `RequestProject/Root/CodingTheory/OrbitThreeAmbiguity.lean`
* **EXACT HYPOTHESES:** finite field; `σ` of order `m` with distinct iterates, fixing `D`
  pointwise; three `σ`-fixed words `u : Fin 3 → (↥D → F)` spanning the pair
  (`f₀ = Σ aⱼuⱼ`, `f₁ = Σ bⱼuⱼ`); the same minimality condition as R12.
* **EXACT CONCLUSION:** `#Bad·(q₀−1) ≤ (e + q₀ + 3)(q₀−1) + |ambigSet k e σ u|·(q₀+1)`, with
  `q₀ = |Fix σ|` and `ambigSet` the set of nonzero rational directions whose word carries two
  distinct codewords within radius `e`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES on the left; the ambiguity term is a genuine
  list-decoding statement (two codewords), strictly stronger than mere proximity.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — the orbit-dimension-three class.
* **QUANTITATIVE COST / CARDINAL BOUND:** a bad set larger than `e + q₀ + 3` forces
  `|ambigSet| ≥ (#Bad − e − q₀ − 3)(q₀−1)/(q₀+1)` ambiguous directions.
* **STRICTLY DECREASING DESCENT MEASURE:** the orbit dimension `d = 3 → 2` (the descent step
  this theorem closes).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The challenge itself: badness is converted into a
  count of *directions*, and scaling classes are identified.
* **SHARPNESS / BARRIER THEOREM:** `OrbitThreeSharpness.lean`; and R20 is its deployed
  quantitative form.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

### R20 — Deployed form on the KoalaBear row: a Prize-breaking pencil forces `2.7·10¹⁷` ambiguous directions

* **DECLARATION:** `Root.CodingTheory.KoalaRow.prizeBreaking_ambiguity_lower_bound` — `RequestProject/Root/CodingTheory/KoalaBearOrbitThreeAmbiguity.lean`
* **EXACT HYPOTHESES:** the deployed KoalaBear parameters (`FKB`, `pKB`, `domKB`, `kKB`);
  `e ≤ nKB`; three Frobenius-fixed words spanning the pair; the minimality condition; and
  `prizeThreshold < |badSet kKB e f₀ f₁|`.
* **EXACT CONCLUSION:** `274980725720479240 ≤ (ambigSet kKB e (frobenius FKB pKB) u).card`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — the Galois-structured class on one fixed row.
* **QUANTITATIVE COST / CARDINAL BOUND:** `≥ 2.7498·10¹⁷` ambiguous rational directions, i.e.
  `≥ 128000000·(p−1)`, more than `1.28·10⁸` points of `PG(2,p)`.
* **STRICTLY DECREASING DESCENT MEASURE:** as R19.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** As R19; in addition the statement is specialised
  to one parameter row, so no asymptotics survive.
* **SHARPNESS / BARRIER THEOREM:** companion `prizeBreaking_forces_ambiguity` (the exact
  relation) and `prizeBreaking_ambiguity_projective` (the `(p−1)`-multiple form) in the same
  file.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

### R21 — Extension-field MCA in the field-reduction normal form

* **DECLARATION:** `Root.CodingTheory.isBad_iff_coord` — `RequestProject/Root/CodingTheory/FieldReductionNormalForm.lean`
* **EXACT HYPOTHESES:** an extension `K/F` with basis `B : Basis ι F K`, a domain `D ⊆ K` whose
  points are images of base-field values (`a` with `algebraMap F K (a x) = x`), arbitrary
  `f₀ f₁ : ↥D → K` and `γ : K`.
* **EXACT CONCLUSION:** `IsBad k e f₀ f₁ γ ↔ ∃ S, n ≤ |S| + e ∧ (∀ i, IsCloseOnBase k S a
  (coordWord B i (f₀ + γ f₁))) ∧ ¬ (∀ δ, ∀ i, IsCloseOnBase k S a (coordWord B i (f₀ + δ f₁)))`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — and this is the point: the support `S` is common to
  *all* `|ι|` coordinate words on both sides of the conjunction.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** none (an equivalence); it is the interface that lets
  base-field (spread/incidence) counting be applied to an extension-field instance.
* **STRICTLY DECREASING DESCENT MEASURE:** the field degree `[K : F] = |ι|`: an instance over
  `K` becomes `|ι|` coupled instances over `F`.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing (iff) — but the coupling between the
  coordinate words must be carried along; dropping it is what makes downstream bounds lossy.
* **SHARPNESS / BARRIER THEOREM:** `SpreadIncidenceBarrier.lean` (the Desarguesian-spread route
  has an intrinsic incidence barrier) and `KoalaBearFieldReduction.lean` for the deployed row.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

---

## 4. Strict-descent records (reductions with an explicit measure)

### R22 — The graded budget law: `#Bad + e·|Z| + corank ≤ (e+1)(ℓ−1)`

* **DECLARATION:** `Root.CodingTheory.PolyGen.Hankel.card_badSetG_add_corank_le` — `RequestProject/Root/CodingTheory/HankelRankProfile.lean`
* **EXACT HYPOTHESES:** finite field; window `i₀ + 2e + k + 1 ≤ n`; non-degeneracy
  `shiftDet l e i₀ f ≠ 0`; a rank bound `rank (scalarHankel e i₀ (f (l−1))) ≤ r`.
* **EXACT CONCLUSION:** `(badSetG l k e f).card + e·|synZeroSet l f| + (e + 1 − r) ≤ (e+1)(l−1)`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — requires the non-degeneracy `shiftDet ≠ 0`.
* **QUANTITATIVE COST / CARDINAL BOUND:** the budget `(e+1)(ℓ−1)` is *shared*: every unit of
  corank of the top moment matrix and every syndrome-zero challenge is subtracted from the
  admissible `#Bad`.
* **STRICTLY DECREASING DESCENT MEASURE:** the corank `e + 1 − r` of the top word — strictly
  positive corank strictly lowers the remaining bad-set budget.  This is the descent measure of
  the whole staircase family (`HankelCumulativeRank.lean` adds the coranks of all windows).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The identity of the challenges; and the
  non-degenerate branch only — degenerate families are handed to R14/R15.
* **SHARPNESS / BARRIER THEOREM:** `HankelExtremal.lean` / `HankelExtremalGates.lean` classify
  equality; `HankelExtremalRSLocalised.lean` builds scalable extremizers, and R35 shows the
  subresultant mechanism is void exactly there.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

### R23 — The two-word cash-out: `#Bad ≤ |T|`, no `k`, no `e`

* **DECLARATION:** `Root.CodingTheory.PolyGen.Hankel.card_badSetG_le_card_support_two` — `RequestProject/Root/CodingTheory/HankelCumulativeRank.lean`
* **EXACT HYPOTHESES:** finite field; window `i₀ + 2e + k + 1 ≤ n`; non-degeneracy
  `shiftDet 2 e i₀ f ≠ 0`; and the top word is explained off `T`: `IsCloseOn k Tᶜ (f 1)`.
* **EXACT CONCLUSION:** `(badSetG 2 k e f).card ≤ T.card`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — non-degeneracy plus a supplied error support `T` for
  the direction word.
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≤ |T|` — the *weight of the error of the
  direction word alone*, with no dependence on rate or radius.
* **STRICTLY DECREASING DESCENT MEASURE:** `|T|`: any improvement of the explanation of the top
  word strictly improves the bound.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Everything about `f 0`; the bound charges the
  whole bad set to the top word.
* **SHARPNESS / BARRIER THEOREM:** `two_word_hankel_lt_subresultant` (same file) compares it with
  the subresultant bound; `not_window_close_of_extremal` marks where the staircase stops.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

### R24 — The shortening transfer inequality

* **DECLARATION:** `Root.CodingTheory.card_badSet_mul_choose_le` — `RequestProject/Root/CodingTheory/ShorteningMCA.lean`
* **EXACT HYPOTHESES:** finite field; a deletion depth `t ≤ k`; and a uniform bound `B` on the
  bad set of *every* shortened instance obtained by pinning a `t`-subset `W` (as a generalised
  RS instance on `D \ W` with dimension `k − t`).
* **EXACT CONCLUSION:** `#Bad · C(n − e, t) ≤ C(n, t) · B`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES on both sides (the shortened instances use the
  GRS same-support bad set).
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES — the pair is arbitrary; the hypothesis is a uniform
  bound over shortened instances, not a structural condition on `(f₀,f₁)`.
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≤ B · C(n,t)/C(n−e,t)`; the transfer factor is
  `(1 − δ)^{−t}` in the limit, i.e. exponential in the depth `t`.
* **STRICTLY DECREASING DESCENT MEASURE:** the deletion depth: `(n, k) → (n − t, k − t)`, and
  the relative radius rises, which is the point of the manoeuvre.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Which shortened instance certifies which
  challenge; the transfer is a double count over `t`-subsets.
* **SHARPNESS / BARRIER THEOREM:** R33 (`not_constant_shortening_for_positive_slack`) and
  `two_pow_le_choose_div_choose`: linear depth costs `2^{Θ(n)}` and no *constant* depth converts
  a post-Johnson relative radius into a sub-Johnson one.  The route is closed as a
  constant-relative-radius method.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

### R25 — Direction-list reduction: `#Bad ≤ 1 + n·|L(f₁, 2e)|`

* **DECLARATION:** `Root.CodingTheory.card_badSet_le_mul_card_rsList` — `RequestProject/Root/CodingTheory/DirectionListReduction.lean`
* **EXACT HYPOTHESES:** finite field only.  No window, no structural condition; arbitrary
  `f₀ f₁`.
* **EXACT CONCLUSION:** `(badSet k e f₀ f₁).card ≤ 1 + n · (rsList D k (2e) f₁).card`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** `1 + n·Λ(2e)` where `Λ(2e)` is the RS list size of the
  *direction word* at radius `2e` — the challenge coordinate is eliminated entirely.
* **STRICTLY DECREASING DESCENT MEASURE:** the number of free coordinates: an MCA instance in
  `(f₀, f₁, γ)` is reduced to a list-decoding instance in `f₁` alone.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The centre `f₀` completely, and the pairing
  between a bad challenge and its codeword.
* **SHARPNESS / BARRIER THEOREM:** `pairwise_route_within_unique_decoding` (same file): the
  reduction controls `#Bad` only through the list of `f₁` at radius `2e`, so the route cannot
  reach past the radius where that list is polynomial — the pairwise barrier.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

### R26 — Spread-weighted incidence: `ε_mca` without the challenge coordinate

* **DECLARATION:** `Root.CodingTheory.epsMCA_le_sum_spreadWeight` — `RequestProject/Root/CodingTheory/SpreadIncidence.lean`
* **EXACT HYPOTHESES:** finite field; arbitrary `k, e, f₀, f₁`.
* **EXACT CONCLUSION:** `epsMCA k e f₀ f₁ ≤ (max 1 (Σ_{p ∈ rsBigPairs k e f₀ f₁}
  spreadWeight e |devActive f₀ f₁ p.1 p.2|)) / q`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — `epsMCA` is the measure of the official `badSet`.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES.
* **QUANTITATIVE COST / CARDINAL BOUND:** an `ε_mca` bound of the form `(Σ weights)/q`; the sum
  ranges over codeword pairs with a big common agreement, weighted by their active deviation
  set.
* **STRICTLY DECREASING DESCENT MEASURE:** the challenge coordinate is eliminated: the remaining
  index set is the pair set `rsBigPairs`, of dimension one lower.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Which challenge belongs to which pair; the bound
  charges each pair its full spread weight.
* **SHARPNESS / BARRIER THEOREM:** `card_badSet_le_succ_radius_mul_card_bigPairs` (same file)
  and `SpreadIncidenceBarrier.lean`: the pair count is the quantity the route cannot bound below
  the Johnson agreement threshold.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

### R27 — Multiplicity stratification of the interleaved list (heavy/light split)

* **DECLARATION:** `Root.CodingTheory.card_badSet_le_heavy_light` — `RequestProject/Root/CodingTheory/WeightedInterleavedList.lean`
* **EXACT HYPOTHESES:** finite field; a multiplicity threshold `2 ≤ M ≤ e + 1` and a radius `r`
  dominating every layer above `M` (`∀ m ≥ M, pairRadius e m ≤ r`); arbitrary `f₀ f₁`.
* **EXACT CONCLUSION:** `#Bad ≤ max 1 ((M−1)·|pairListProfile k (2e) f₀ f₁| +
  (e+2−M)·|pairListProfile k r f₀ f₁|)`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES (the hypothesis constrains `M, r`, not the words).
* **QUANTITATIVE COST / CARDINAL BOUND:** `(M−1)·L₂(2e) + (e+2−M)·L₂(r)`; the deployed pivot is
  `M = 16` (`DeployedWeightedList.lean`).
* **STRICTLY DECREASING DESCENT MEASURE:** the multiplicity threshold `M`: raising `M` moves
  layers from the expensive radius `2e` to the small radius `r`, and the layer index strictly
  decreases along the stratification.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The individual multiplicities inside a layer;
  each layer is charged its worst case.
* **SHARPNESS / BARRIER THEOREM:** `card_badSet_le_of_no_heavy` (the complementary branch) and
  `card_pairListProfile_mul_choose_le` bound the profile; a bad set beyond `(M−1)·L₂(2e)`
  *forces* a codeword pair at block radius `r`, which is the barrier the layer cake exposes.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

### R28 — Witness elimination for far-centred lines

* **DECLARATION:** `Root.CodingTheory.WitnessElimination.card_badSet_le_of_polynomial_witness_family` — `RequestProject/Root/CodingTheory/WitnessElimination.lean`
* **EXACT HYPOTHESES:** finite field; far centre `e < distToCode k f₀`; a polynomial family
  `P : F[X][X]` with `deg (P.coeff 0) < k`, such that every close challenge is witnessed by the
  specialisation `familyWitness P γ` agreeing off `e` positions.
* **EXACT CONCLUSION:** `(badSet k e f₀ f₁).card ≤ n · max P.natDegree 1`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES on the conclusion; the hypothesis is stated on
  `goodZ` (proximity only), which makes it *weaker* to assume and hence the theorem stronger.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — far centres carrying a polynomial witness family.
* **QUANTITATIVE COST / CARDINAL BOUND:** `n · max(deg P, 1)`, i.e. `O(n)` for a bounded-degree
  family; `card_goodZ_le_of_witness_families` extends it to finitely many families.
* **STRICTLY DECREASING DESCENT MEASURE:** `deg P`: eliminating a witness family lowers the
  degree that has to be charged.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The individual witness polynomial per challenge —
  replaced by one algebraic family.
* **SHARPNESS / BARRIER THEOREM:** `WITNESS_ELIMINATION_REPORT.md` records that the hypothesis
  (existence of a bounded-degree witness family) is exactly what fails on the extremal locus of
  R35; without it no bound of this shape holds.
* **PROOF STATUS:** Lean.
* **ROLE:** `STRICT_DESCENT`

---

## 5. Meta-barrier records (negative results, lower bounds, closed routes)

### R29 — The forcing frontier: unique below `k + 2e ≤ n`, no output above it

* **DECLARATION:** `Root.CodingTheory.forcing_unique_at_frontier` and
  `Root.CodingTheory.forcing_not_unique_beyond_frontier` — `RequestProject/Root/CodingTheory/ForcingBarrier.lean`
* **EXACT HYPOTHESES:** (a) `1 ≤ k`, `k + 2e ≤ n`, `S` with `n ≤ |S| + 2e`, `p, q` of degree
  `< k` agreeing on `S`.  (b) `1 ≤ k`, `n < k + 2e`, and an arbitrary word `u : F → F`.
* **EXACT CONCLUSION:** (a) `p` and `q` agree on all of `D`.  (b) there is `S ⊆ D` with
  `|S| = n − 2e` and two *distinct* polynomials of degree `< k` both interpolating `u` on `S`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a — a statement about the forcing step, which is the
  mechanism used to extract a common support; it is what makes same-support extraction possible
  below the frontier.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES (both parts quantify over all data).
* **QUANTITATIVE COST / CARDINAL BOUND:** the frontier is exactly `δ ≤ (1−ρ)/2`; the second part
  shows the canonical pair extracted from two bad challenges is *undefined* past it.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** n/a.
* **SHARPNESS / BARRIER THEOREM:** this pair *is* the barrier statement: every Welch–Berlekamp /
  pencil / subresultant route of the repository (R3, R13, R28, R35) stops at `k + 2e = n` for
  this reason, and no repair inside the mechanism is possible.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R30 — The subspace pencil: `#Bad` beats every fixed polynomial at a vanishing capacity gap

* **DECLARATION:** `Root.CodingTheory.exists_superpolynomial_badSet_of_small_relative_gap` — `RequestProject/Root/CodingTheory/SubspacePencil.lean`
* **EXACT HYPOTHESES:** a prime `p`; arbitrary `d M : ℕ` (target polynomial degree and inverse
  relative gap).
* **EXACT CONCLUSION:** `∃ N, ∀ field K of characteristic p with p^N < |K|, ∃ D, k, e, c, f₀, f₁`
  with `n = k + e + c`, `1 ≤ c`, `M·c ≤ n` and `n^d < (badSet k e f₀ f₁).card`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — the challenges produced are bad in the official
  same-support sense.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — an existence statement: one explicit pencil
  (`f₀(x) = x^{p^ℓ}`, `f₁ = 1_w`, `D = U ∪ {w}`).
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≥ p^{ℓ(m−ℓ)}` with `n = p^m + 1`,
  `k = p^{ℓ−1}+1`, `e = n − p^ℓ − 1`; relative gap `η = c/n ≤ 1/M`.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing — an explicit construction.
* **SHARPNESS / BARRIER THEOREM:** `SubspacePencilAudit.lean`: `subspacePencil_superpoly_forces_gap`
  and `subspacePencil_gap_lt_of_superpoly` (beating `n^d` forces `m − ℓ > d`, i.e. gap below
  `p^{−d}`) and `subspacePencil_vanishing_gap_linear_bound` (at `ℓ = 1` the family gives only a
  linear bound).  So the record refutes the conjectural gap-layer law
  `max #Bad ≈ poly(n) + exp(Θ(1/η))`, and does *not* claim superpolynomiality at every
  vanishing gap.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R31 — Exponentially many bad challenges one coordinate below capacity

* **DECLARATION:** `Root.CodingTheory.four_pow_le_card_badSet_twoPowDomain` — `RequestProject/Root/CodingTheory/CapacityGapPencil.lean`
* **EXACT HYPOTHESES:** a prime `p` with `2^{2(k+1)} < p`; domain `twoPowDomain p (2(k+1))` of
  size `n = 2(k+1)`, dimension `k`, radius `e = k+1` (rate `≈ 1/2`, one coordinate below the
  capacity radius); the explicit line `f₀(x) = x^{k+1}`, `f₁(x) = x^k`.
* **EXACT CONCLUSION:** `4^{k+1} ≤ 2(k+1) · (badSet k (k+1) f₀ f₁).card`, i.e.
  `#Bad ≥ 4^{k+1}/n = 2^n/n`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — one explicit pencil.
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≥ 2^n/n`; the companion
  `choose_div_card_le_epsMCAmax_twoPowDomain` turns it into an `ε_mca` lower bound.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing.
* **SHARPNESS / BARRIER THEOREM:** it *is* the barrier for the capacity regime: no polynomial
  bound on `#Bad` can hold at `e = n − k − 1`, so every polynomial certificate must keep a
  positive capacity gap.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R32 — Saturation: a family with `p − 1` bad challenges out of `p`

* **DECLARATION:** `Root.CodingTheory.PolyGen.Saturation.card_badSetG_satFam_zmod_ge` — `RequestProject/Root/CodingTheory/AmbiguitySaturation.lean`
* **EXACT HYPOTHESES:** a prime `p ≥ 4`; the explicit arity-2 family `satFam (ZMod p)` at
  `k = |F| − 2`, `e = 1`.
* **EXACT CONCLUSION:** `p − 1 ≤ (badSetG 2 (Fintype.card (ZMod p) − 2) 1 (satFam (ZMod p))).card`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES; moreover `card_ambiguousSet_satFam_ge` shows a
  positive fraction of them are genuinely *ambiguous*, not merely bad.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — one explicit family.
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≥ q − 1`, i.e. `ε_mca ≥ (q−1)/q`: the global
  gate is saturated.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing.
* **SHARPNESS / BARRIER THEOREM:** it is the scalable barrier for *window-free* bounds (R7) and
  for every windowed dichotomy (R14, R15): `satFam_outside_window` records that it sits exactly
  one step outside the window `k + (ℓ+1)e ≤ n`, and any bound valid at every `(k,e)` must be
  vacuous here.  Small cases are decided in
  `SparseDomainSharpness.lean` (`four_le_card_badSetG_satFam_five`).
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R33 — No constant-depth shortening converts a post-Johnson radius into a sub-Johnson one

* **DECLARATION:** `Root.CodingTheory.not_constant_shortening_for_positive_slack` — `RequestProject/Root/CodingTheory/ChojeckiRadius.lean`
* **EXACT HYPOTHESES:** reals `0 < ρ < 1`, `1 − √ρ < δ < 1`, and any fixed depth `t : ℕ`.
* **EXACT CONCLUSION:** `∃ N, ∀ n ≥ N, ((n − ⌊δn⌋) − t)² ≤ (n − t)(⌊ρn⌋ − t − 1)` — the
  shortened instance is still not sub-Johnson.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a — an inequality about parameters, applied to the
  same-support transfer R24.
* **UNIFORM OVER ALL RECEIVED PAIRS?** YES (parameter-level, pair-free).
* **QUANTITATIVE COST / CARDINAL BOUND:** together with `two_pow_le_choose_div_choose`, linear
  depth costs a factor `2^{Θ(n)}`.
* **STRICTLY DECREASING DESCENT MEASURE:** none (it kills a proposed descent).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** n/a.
* **SHARPNESS / BARRIER THEOREM:** this is the sharpness statement for R24.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R34 — The dimension-based sub-Johnson hypothesis is false

* **DECLARATION:** `Root.CodingTheory.subJohnsonBoundPoly_false` — `RequestProject/Root/CodingTheory/SubJohnsonRefutation.lean`
* **EXACT HYPOTHESES:** any deletion depth `t` and any constant `C`.
* **EXACT CONCLUSION:** `¬ SubJohnsonBoundPoly.{0} t C` — the counterexample has `k = 1` over a
  prime field of length `p > t + 64C + 2`, budget `e = p − t − 2`, and at least `p − t − 2` bad
  parameters against the claimed bound `64C`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — the counterexample's challenges are officially bad.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO (a refutation, hence one family).
* **QUANTITATIVE COST / CARDINAL BOUND:** `#Bad ≥ p − t − 2` versus the hypothesised `C(k+1)⁶`.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** n/a.
* **SHARPNESS / BARRIER THEOREM:** the failure is structural, not accidental: a bad-parameter
  bound that does not grow with the *length* cannot hold; the corrected hypothesis is
  `SubJohnsonBoundLen`.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R35 — The subresultant description is void on the localised extremal locus

* **DECLARATION:** `Root.CodingTheory.PolyGen.Hankel.exists_root_W_can_not_close_of_localised` — `RequestProject/Root/CodingTheory/HankelSubresultantBridge.lean`
* **EXACT HYPOTHESES:** finite field; `1 ≤ k`, `k + 2e + 1 ≤ n`; two codewords `q 0, q 1` of
  degree `< k` explaining the two words off a set `W` with `|W| = e + 1` and nonvanishing error
  polynomial on `W` (the localised extremal class); `e + 1 < |F|`.
* **EXACT CONCLUSION:** `∃ γ, (W_can k e (f 0) (f 1)).eval γ = 0 ∧ ¬ IsCloseToCode k e
  (f 0 + γ·f 1)` — a root of the canonical subresultant witness that is *not* close.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a — it refutes an identity between the close locus and
  a root locus; the close side is the proximity notion.
* **UNIFORM OVER ALL RECEIVED PAIRS?** NO — the localised class (which is exactly the extremal
  locus of the Hankel budget law R22).
* **QUANTITATIVE COST / CARDINAL BOUND:** none; the point is that `W_can ≡ 0` there, so the root
  locus is all of `F` and carries no information.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** n/a.
* **SHARPNESS / BARRIER THEOREM:** this is the barrier: the `KernelNonzero` hypothesis of the
  subresultant gate is not a technicality, and the Hankel and subresultant mechanisms do not
  compose on the extremal locus.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R36 — The `r`-block lower bound: `ε_mca ≥ r/q`

* **DECLARATION:** `Root.CodingTheory.card_le_epsMCAmax_of_blocks` — `RequestProject/Root/CodingTheory/MCALowerBound.lean`
* **EXACT HYPOTHESES:** finite field; `0 < r ≤ |F|` and `r · max (n − e) (k+1) ≤ n`.
* **EXACT CONCLUSION:** `(r : ℝ)/q ≤ epsMCAmax k e D`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** YES — `epsMCAmax` is the max over lines of the official
  measure.
* **UNIFORM OVER ALL RECEIVED PAIRS?** It is a statement about the *maximum* over pairs, hence
  witnessed by one explicit line (block word).
* **QUANTITATIVE COST / CARDINAL BOUND:** `ε_mca ≥ r/q`; at `r = 1` this is the universal floor
  `1/q`, which every upper bound in this package must respect.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing.
* **SHARPNESS / BARRIER THEOREM:** it *is* the scale-setting barrier: no method can prove
  `ε_mca < 1/q`, so a `2^{-128}` target forces `q ≥ 2^{128}` regardless of the mechanism.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

---

## 6. FFT / M31 records (the algorithmic layer of the package)

These four records are stated in the same format for uniformity, but the MCA-specific fields
(*same support*, *received pairs*) do not apply to them; they are marked `n/a`.

### R37 — Correctness of the radix-2 Cooley–Tukey recursion, with exact operation counts

* **DECLARATION:** `FFT.fftRec_eq_dft` (with `FFT.fftMuls_eq`, `FFT.fftAdds_eq`,
  `FFT.fftMulsOpt_eq`, `FFT.fftRec_inversion`) — `RequestProject/CooleyTukey.lean`
* **EXACT HYPOTHESES:** a field `F`, `ζ` with `ζ^(2^k) = 1` (no primitivity needed for
  correctness; primitivity `IsPrimitiveRoot ζ (2^k)` is needed only for inversion).
* **EXACT CONCLUSION:** `∀ k ζ, ζ^(2^k) = 1 → ∀ a j, fftRec k ζ a j = dft (2^k) ζ a j`; the
  counts `fftMuls k = k·2^k`, `fftAdds k = k·2^k`, `2·fftMulsOpt k = k·2^k`, and
  `dft (2^k) ζ⁻¹ (fftRec k ζ a) m = 2^k · a m`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a.
* **UNIFORM OVER ALL RECEIVED PAIRS?** n/a (uniform in all inputs `a` and all `k`).
* **QUANTITATIVE COST / CARDINAL BOUND:** `k·2^k` multiplications and additions, halved to
  `k·2^{k−1}` by the twiddle-symmetry optimisation, against `dftMulsDirect k = 4^k` for the
  direct transform (`fftMulsOpt_lt_direct`).
* **STRICTLY DECREASING DESCENT MEASURE:** the recursion depth `k` (each step halves the length).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing — an exact equality with the DFT.
* **SHARPNESS / BARRIER THEOREM:** the model-level comparisons `Radix4.lean`, `Radix8.lean`,
  `ExtensionVsCircle.lean` decide which radix wins in this cost model; R38 is the exact
  lower-bound statement for the associated bilinear problem.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R38 — The exact bilinear complexity of cyclic convolution over `M31`

* **DECLARATION:** `FFT.Bilinear.cyclicConv_M31_two_pow_bilinear_complexity` — `RequestProject/CyclotomicFactorCount.lean`
* **EXACT HYPOTHESES:** `1 ≤ k ≤ 29`.
* **EXACT CONCLUSION:** there is a convolution algorithm `C : ConvAlg M31 (ZMod (2^k))` with
  `C.Computes` and `C.k = 3·2^{k−1} − 1`, **and** every computing algorithm has
  `3·2^{k−1} − 1 ≤ C.k`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a.
* **UNIFORM OVER ALL RECEIVED PAIRS?** n/a (uniform over all algorithms in the bilinear model).
* **QUANTITATIVE COST / CARDINAL BOUND:** exactly `3·2^{k−1} − 1` general multiplications; at
  `k = 20`, `cyclicConv_M31_two_pow_twenty` gives the deployed value.
* **STRICTLY DECREASING DESCENT MEASURE:** none (it is an exact value, proved via the Frobenius
  orbit/cyclotomic coset decomposition of `X^{2^k} − 1` over `M31`).
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing: upper and lower bound coincide.
* **SHARPNESS / BARRIER THEOREM:** the statement contains its own sharpness (matching lower
  bound); the range `k ≤ 29` is exactly where the required roots of unity exist in `M31`.
* **PROOF STATUS:** Lean.
* **ROLE:** `FINITE_CHALLENGE_COST`

### R39 — Which circle-FFT twiddles are free rotations: the exact (negative) answer

* **DECLARATION:** `FFT.Circle.MersenneFree.circleTw_free` and
  `FFT.Circle.MersenneFree.freeLevel_card` — `RequestProject/CircleFreeTwiddles.lean`
* **EXACT HYPOTHESES:** `q : Circle M31` with `q^(2^{m+2}) = 1` and `m + 2 ≤ 27`; a twiddle
  `circleTw q m k i` that is a power of two.
* **EXACT CONCLUSION:** that twiddle equals `1` or `2¹⁵`; and, for every `m ≤ 31`, the number of
  admissible `x`-coordinates is `1, 2, 3, 5, 8, 16` according to
  `m ≤ 2`, `3 ≤ m ≤ 27`, `m = 28`, `29`, `30`, `31`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a.
* **UNIFORM OVER ALL RECEIVED PAIRS?** n/a (uniform over all levels `k` and indices `i`).
* **QUANTITATIVE COST / CARDINAL BOUND:** at most two free values for every transform size up to
  `2²⁷`, and never more than sixteen up to the whole circle group `2³¹`.
* **STRICTLY DECREASING DESCENT MEASURE:** the doubling map `π(x) = 2x² − 1` on `x`-coordinates:
  `p^{2^k} = 1 ↔ π^k(p.x) = 1` reduces the question to a finite base-field iteration, with `k`
  strictly decreasing.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** The `y`-coordinate: only `x` matters for freeness.
* **SHARPNESS / BARRIER THEOREM:** both bounds are attained — `pt45` is a genuine point of order
  8 realising `2¹⁵`, and `pt27` has order `2²⁸`, where a third free value appears.  So the
  free-rotation optimisation cannot be pushed further.
* **PROOF STATUS:** Lean.
* **ROLE:** `META-BARRIER`

### R40 — The isotypic decomposition as a single natural isomorphism `diag ≅ forget`

* **DECLARATION:** `FFT.diagNatIso` (with `FFT.diagNatIso_hom_apply`, `FFT.dftModes`,
  `FFT.diagNatIso_inv_app`, and the Mersenne instance `FFT.M31.diagNatIso31`) — `RequestProject/IsotypicNatIso.lean`
* **EXACT HYPOTHESES:** a field `K`, `n` with `NeZero n`, `ζ` a primitive `n`-th root of unity
  in `K`, and `n` invertible in `K` (`(n : K) ≠ 0`).
* **EXACT CONCLUSION:** `diagFunctor ζ n ≅ Action.forget (ModuleCat K) (CycGroup n)`, an
  isomorphism of functors on `Rep K C_n`; forwards it sums the isotypic components, backwards it
  takes the Fourier modes `(1/n)·Σ_k ζ^{−jk} ρ(g)^k v`.
* **OFFICIAL SAME-SUPPORT PRESERVED?** n/a.
* **UNIFORM OVER ALL RECEIVED PAIRS?** n/a — but it *is* natural, i.e. uniform over all objects
  and all intertwiners of `Rep K C_n`, which is the corresponding uniformity statement here.
* **QUANTITATIVE COST / CARDINAL BOUND:** none (a structural isomorphism); its computational
  content is the DFT and its inverse.
* **STRICTLY DECREASING DESCENT MEASURE:** none.
* **WHICH DATA ARE LOST UNDER THE REDUCTION?** Nothing — an isomorphism, with both directions
  computed explicitly.
* **SHARPNESS / BARRIER THEOREM:** the hypotheses are exactly the classical ones (`ζ` primitive
  and `n` invertible); without them the eigenspace sum is not internal.
* **PROOF STATUS:** Lean.
* **ROLE:** `RIGIDITY`

---

## 7. Role index

| Role | Records |
|---|---|
| `RIGIDITY` | R14, R15, R16, R17, R18, R19, R20, R40 |
| `STRICT_DESCENT` | R21, R22, R23, R24, R25, R26, R27, R28 |
| `FINITE_CHALLENGE_COST` | R1, R3, R4, R6, R7, R8, R9, R10, R11, R12, R13, R37, R38 |
| `META-BARRIER` | R2, R5, R29, R30, R31, R32, R33, R34, R35, R36, R39 |

### Cross-cutting notes for the (later) integration step

1. **Same support is preserved everywhere it is claimed.**  Every record answering YES is
   phrased in `IsBad`/`badSet` (or `IsBadG`/`badSetG`/`Alphabet.badSet`), all of which carry the
   one-common-`S` quantifier; R2 certifies that this is the literature notion.  The only places
   where the weaker proximity notion `goodZ` appears are *hypotheses* (R13, R28), which makes
   those theorems stronger, not weaker.
2. **Uniformity is the real currency.**  Only R3, R4, R6, R7, R8, R9, R18, R24, R25, R26, R27
   are uniform over all received pairs; everything else buys its strength from a structural
   class (far centre, rigid/localised family, Galois-orbit span, or one explicit pencil).  An
   integration that chains a uniform record with a class-restricted one must discharge the class
   condition, and that discharge is not in this package.
3. **The floor and the ceiling.**  R36 (`ε_mca ≥ 1/q`) is the floor every upper bound respects;
   R31 and R32 are the ceilings (`#Bad ≥ 2^n/n` near capacity; `#Bad ≥ q − 1` for a saturating
   family), and R29 is the structural wall at `k + 2e = n` behind which all pencil mechanisms
   stop.
4. **No record is conditional.**  All forty are Lean theorems of this repository; where a
   hypothesis is itself conjectural in the literature (a supplied list size, a witness family),
   it appears explicitly in EXACT HYPOTHESES and the record is a theorem *about* that hypothesis.
