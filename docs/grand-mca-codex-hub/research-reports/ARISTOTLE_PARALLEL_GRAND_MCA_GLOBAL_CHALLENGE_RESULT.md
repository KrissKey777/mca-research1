# Grand MCA — global challenge annihilator: result report

**Terminal status: `ANNIHILATOR_OBSTRUCTION` + `NEW_SMALLEST_GATE`.**

`GRAND_MCA_SAFE` is **not** claimed, `OFFICIAL_COUNTEREXAMPLE` is **not** claimed, and no
numerical bound on `#Bad` is claimed anywhere in this run. What is delivered is:

1. a **global** (support-free) locator/syndrome certificate for official badness, proved from the
   official `IsBad` and usable for every fixed official pair;
2. an **exact obstruction**: the eliminant of that certificate, taken *without* the splitting
   constraint on the locator, is identically zero at the deployed row — with the exact defect
   `e + 1 − w = 909313` and the exact consequence that any annihilator obtained from it has
   degree `≥ |F|`;
3. the **single smallest remaining implication** (`NEW_SMALLEST_GATE`): one cardinality bound for
   one globally defined set, which implies the deployed row in both its counting and its
   probabilistic form;
4. an audit of what the strongest known lower-bound family gives at the deployed row
   (`11440 ≪ B*`), and an audit of the deployed budget arithmetic (one figure in the mission
   statement is wrong; see §6).

Everything below is machine-checked in Lean 4 / Mathlib, `sorry`-free, `native_decide`-free, and
axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).

---

## 0. Objects, field, quantifiers, conventions

* **Field and challenge domain.** `F` is an arbitrary field, `[Fintype F]` where cardinalities of
  challenge sets are taken. Challenges range over all of `F`. No property of the KoalaBear prime
  or of an extension degree is used or assumed anywhere; the results specialise to the deployed
  field verbatim.
* **Domain.** `D : Finset F` arbitrary, `|D| = n`. The deployed statements add `hD : D.card =
  2097152`. Where `Xⁿ − 1` appears, the root-of-unity hypothesis on `D` is *explicit* (§5).
* **Official badness.** `Root.CodingTheory.IsBad k e f₀ f₁ γ`: some `S` with `|D| ≤ |S| + e`
  witnesses `IsCloseOn k S (f₀ + γ·f₁)` while `¬ LineCloseOn k S f₀ f₁` (`MCA.lean`, unchanged).
  `badSet k e f₀ f₁ = {γ | IsBad …}` as a `Finset F`.
* **Support/erasure convention.** Erasures are `E : Finset ↥D`, windows are complements `Eᶜ`;
  exact-size normalisation `|E| = e` is the already proved
  `MaxErasure.isBad_iff_exists_exact_erasure`. Locators are the project's
  `ErasureSpan.qPoly (dval D) E = ∏_{a∈E}(X − a)`, monic of degree `|E|`.
* **Parameters (deployed row).** `n = 2097152`, `k = 1048576`, `e = 978944`, `t = n − e = 1118208
  = k + w`, `w = n − k − e = 69632`, `B* = 274980728111395087`.
* **Source replay.** Everything imported (`MCA.lean`, `MaximalErasureNormalization.lean`,
  `ErasureSpanPolynomial.lean`, `CapacityGapPencil.lean`, `ExtremalMCA.lean`) is used as a black
  box and is unmodified; all new material is additive. The two new modules were built from
  source in this run (§7).

New files:

* `RequestProject/Root/CodingTheory/GlobalChallengeAnnihilator.lean` (§1–§6),
* `RequestProject/Root/CodingTheory/GrandMcaGlobalGate.lean` (§4),
* `RequestProject/GlobalChallengeAnnihilatorAxiomAudit.lean`,
  `RequestProject/GrandMcaGlobalGateAxiomAudit.lean` (axiom audits).

---

## 1. The global syndrome functional (definition, support-free)

```lean
noncomputable def gsynd (f : ↥D → F) : F[X] →ₗ[F] F where
  toFun u := ∑ a : ↥D, f a * (lam D a * u.eval (a : F))
```

`lam` is the project's fixed GRS multiplier `λ_a = (∏_{b≠a}(a−b))⁻¹` (`MaxErasure.lam`), which is
independent of every erasure. Hence `gsynd f₀`, `gsynd f₁` are **two fixed linear functionals on
`F[X]` attached to the official pair**, not to a selected support. Two compatibility lemmas are
proved: `gsynd_eq_pairing_psi` (`gsynd f u = ⟨f, Ψ(u)⟩`) and `lambdaMap_psi`
(`Λ(Ψ u) = (gsynd f₀ u, gsynd f₁ u)`), so the functional is exactly the source-native pairing
against the common dual adapter `Ψ`; `gsynd_lineComb` gives
`gsynd (f₀ + γ·f₁) u = gsynd f₀ u + γ·gsynd f₁ u`.

## 2. The key equation (universal, elementary, replayed from source)

```lean
theorem gsynd_locator_eq_zero {k w : ℕ} {E : Finset ↥D} {g : ↥D → F} {p h : F[X]}
    (hdeg : k + E.card + w ≤ D.card)
    (hp : p.degree < (k : WithBot ℕ)) (hh : h.degree < (w : WithBot ℕ))
    (hagree : ∀ x : ↥D, x ∉ E → g x = p.eval (x : F)) :
    gsynd g (qPoly (dval D) E * h) = 0
```

*Universal; no duality theorem used.* Proof: `Q_E` kills the coordinates in `E`, agreement kills
the rest, so the sum equals `∑_a λ_a (p·Q_E·h)(a)` with `deg (p·Q_E·h) ≤ k + |E| + w − 2 ≤ n − 2`,
and `MaxErasure.sum_lam_eval_eq_zero` makes it vanish. At the deployed row `k + e + w = n`
exactly, so the hypothesis holds with no slack.

Two derived forms:

* `locatorSystem_of_monomials` — the system needs only the monomials `X^j`, `j < w`;
* `locatorSystem_of_isCloseOn` — an exact-size window gives the full system for `Q_E`.

## 3. The global locator certificate of official badness (bridge)

```lean
def LocatorSystem (w : ℕ) (f₀ f₁ : ↥D → F) (γ : F) (Q : F[X]) : Prop :=
  ∀ h : F[X], h.degree < (w : WithBot ℕ) → gsynd f₀ (Q * h) + γ * gsynd f₁ (Q * h) = 0

theorem isBad_locator_certificate {k e : ℕ} (hkD : k ≤ D.card)
    (he : e < D.card - k) (heD : e < D.card) (hw : 1 ≤ D.card - k - e)
    {f₀ f₁ : ↥D → F} {γ : F} (hbad : IsBad k e f₀ f₁ γ) :
    ∃ E : Finset ↥D, E.card = e ∧
      LocatorSystem (D.card - k - e) f₀ f₁ γ (qPoly (dval D) E) ∧
      ∃ h : F[X], h.degree < ((D.card - k - e : ℕ) : WithBot ℕ) ∧
        gsynd f₁ (qPoly (dval D) E * h) = 1 ∧ gsynd f₀ (qPoly (dval D) E * h) = -γ
```

*Universal, composes with official `IsBad` directly.* The system comes from §2; the *normalised*
nondegeneracy witness (`gsynd f₁ = 1`, `gsynd f₀ = −γ` simultaneously) comes from the proved
adapter `wSpace_eq_wModel` (`W_E = Ψ(Q_E·F[X]_{<w})`) together with the projective label
`lamImage_eq_span` (`Λ(W_E) = F·(−γ,1)`). So the exact source relation `s₀ + Y·s₁ ∈ V_E`,
`s₁ ∉ V_E` is replayed, not assumed, and the linear challenge image is connected to official
badness through the source adapter, never by fiat.

## 4. The gate (`NEW_SMALLEST_GATE`)

```lean
noncomputable def locatorChallengeSet (k e : ℕ) (f₀ f₁ : ↥D → F) : Set F :=
  {γ : F | ∃ E : Finset ↥D, E.card = e ∧
      LocatorSystem (D.card - k - e) f₀ f₁ γ (qPoly (dval D) E) ∧
      LocatorNondeg (D.card - k - e) f₁ (qPoly (dval D) E)}

theorem badSet_subset_locatorChallengeSet …     -- ↑(badSet k e f₀ f₁) ⊆ locatorChallengeSet k e f₀ f₁
theorem card_badSet_le_of_locatorChallengeSet_le … (hB : (locatorChallengeSet k e f₀ f₁).ncard ≤ B) :
    (badSet k e f₀ f₁).card ≤ B
theorem deployed_card_badSet_le_of_gate (hD : D.card = 2097152) (f₀ f₁ : ↥D → F)
    (hgate : (locatorChallengeSet 1048576 978944 f₀ f₁).ncard ≤ 274980728111395087) :
    (badSet 1048576 978944 f₀ f₁).card ≤ 274980728111395087
```

and, in `GrandMcaGlobalGate.lean`, the packaged form

```lean
def DeployedSplitLocatorGate (D : Finset F) : Prop :=
  ∀ f₀ f₁ : ↥D → F, (locatorChallengeSet 1048576 978944 f₀ f₁).ncard ≤ 274980728111395087

theorem deployed_grand_mca_of_gate  (hD : D.card = 2097152) (hgate : DeployedSplitLocatorGate D)
    (f₀ f₁ : ↥D → F) : (badSet 1048576 978944 f₀ f₁).card ≤ 274980728111395087
theorem deployed_epsMCAmax_le_of_gate (hD : D.card = 2097152) (hgate : DeployedSplitLocatorGate D) :
    epsMCAmax 1048576 978944 D ≤ (274980728111395087 : ℕ) / (Fintype.card F : ℝ)
```

the second through the repository's already proved equivalence
`Root.CodingTheory.deployed_security_iff`.

**The single smallest remaining implication** is therefore exactly:

> For the fixed official pair `(f₀,f₁)` on the deployed domain, the set of scalars `γ` for which
> some **monic degree-`e` polynomial split over `D`** (equivalently: some minimum-weight codeword
> of `RS_{e+1}(D)`, equivalently — for a root-of-unity domain — some degree-`e` divisor of
> `Xⁿ − 1`) lies in the kernel of the `w`-row global system `A + γB` **nondegenerately**, has at
> most `B* = 274980728111395087` elements.

Everything to the left of that gate is proved above; nothing else in this run depends on it.

## 5. The exact obstruction (`ANNIHILATOR_OBSTRUCTION`)

The gate cannot be discharged by eliminating the locator from the linear system alone. Write the
system as one global linear map

```lean
noncomputable def locLin (w : ℕ) (f₀ f₁ : ↥D → F) (γ : F) : F[X] →ₗ[F] (Fin w → F) :=
  Q ↦ fun j => gsynd f₀ (Q * X ^ (j : ℕ)) + γ * gsynd f₁ (Q * X ^ (j : ℕ))
```

restricted to `F[X]_{<e+1}`. Then

```lean
theorem finrank_ker_locLin_ge (w e : ℕ) (f₀ f₁ : ↥D → F) (γ : F) :
    e + 1 - w ≤ Module.finrank F (LinearMap.ker (locLinRestrict w e f₀ f₁ γ))

theorem exists_nonzero_locator {w e : ℕ} (hwe : w ≤ e) (f₀ f₁ : ↥D → F) (γ : F) :
    ∃ Q : F[X], Q ≠ 0 ∧ Q.degree < ((e + 1 : ℕ) : WithBot ℕ) ∧ LocatorSystem w f₀ f₁ γ Q

theorem unconstrainedLocatorSet_eq_univ {w e : ℕ} (hwe : w ≤ e) (f₀ f₁ : ↥D → F) :
    unconstrainedLocatorSet w e f₀ f₁ = Set.univ

theorem deployed_unconstrained_annihilator_degree_ge [Fintype F] (f₀ f₁ : ↥D → F)
    {R : F[X]} (hR : R ≠ 0)
    (hvanish : ∀ γ ∈ unconstrainedLocatorSet 69632 978944 f₀ f₁, R.eval γ = 0) :
    Fintype.card F ≤ R.natDegree ∧ (978944 : ℕ) + 1 - 69632 = 909313
```

*Universal statements (the first three), plus one computational instance at the deployed row.*

Reading. At the deployed row the locator space has dimension `e + 1 = 978945` while the system
has only `w = 69632` rows, so the kernel has dimension at least `909313` **for every challenge**.
Consequently the locus cut out by "there exists a nonzero locator of degree `≤ e` solving the
system" is all of `F`; every nonzero polynomial annihilating it has at least `|F|` roots, i.e.
degree `≥ |F| > B*`. **The unconstrained eliminant is identically zero.** This triggers the
mission's stop rule verbatim, and it is the *dual* (locator/syndrome) form of the primal fact
already in the repository, `Root.CodingTheory.exists_nonzero_wbVector_of_card_lt`
(`WelchBerlekampPencil.lean`): both are the single inequality `n < k + 2e + 1`, i.e. `w ≤ e`.
The two routes are therefore the same obstruction and neither is a way around the other.

What survives the obstruction is precisely the datum the linear algebra discards: the locator
must be **split over `D`** with `e` distinct roots. That constraint is not linear, is not
determinantal in `γ`, and is exactly the content of the gate of §4.

**Locator/divisibility convention, verified** (the mission asked that `Q_E ∣ Xⁿ − 1` not be
assumed):

```lean
theorem qPoly_dvd_domainVanishing (E : Finset ↥D) :
    qPoly (dval D) E ∣ qPoly (dval D) (Finset.univ : Finset ↥D)
theorem domainVanishing_eq_X_pow_sub_one {n : ℕ} (hn : 0 < n) (hcard : D.card = n)
    (hroot : ∀ a ∈ D, a ^ n = 1) : qPoly (dval D) (Finset.univ : Finset ↥D) = X ^ n - 1
theorem qPoly_dvd_X_pow_sub_one {n : ℕ} (hn : 0 < n) (hcard : D.card = n)
    (hroot : ∀ a ∈ D, a ^ n = 1) (E : Finset ↥D) : qPoly (dval D) E ∣ (X ^ n - 1 : F[X])
```

So `Q_E ∣ Xⁿ − 1` holds **iff the evaluation domain is a full set of `n` distinct `n`-th roots of
unity**; for a general domain only `Q_E ∣ ∏_{a∈D}(X − a)` is available. The deployed domain (a
multiplicative subgroup of order `2²¹`) satisfies the hypothesis, but the hypothesis is now
explicit in every statement that uses it.

## 6. Audits

### 6.1 Deployed budget ledger (computational, `norm_num`)

```lean
theorem deployed_budget_ledger :
    2097152 = 1048576 + 978944 + 69632 ∧ 1118208 = 2097152 - 978944 ∧ 1118208 = 1048576 + 69632 ∧
      69632 ^ 3 = 337618789203968 ∧ 2097152 * 69632 ^ 2 = 10168283533672448 ∧
      2097152 ^ 2 * 69632 = 306244774661193728 ∧
      69632 ^ 3 < 2097152 * 69632 ^ 2 ∧ 2097152 * 69632 ^ 2 < 274980728111395087 ∧
      274980728111395087 < 2097152 ^ 2 * 69632
```

The mission's `w³` and `n·w²` figures are confirmed exactly. **The mission's `n²w` figure is
wrong**: it states `306244774661193700`, the true value is `306244774661193728` (`= 2⁵⁴·17`). The
qualitative claim is unaffected — `n²w > B*` either way — but the constant should be corrected in
downstream ledgers.

### 6.2 What the strongest known lower-bound family reaches at the deployed row

The capacity-gap block pencil of the repository (`Root.CodingTheory.card_badSet_ge_blocks`)
requires the gap `c` to satisfy `c ∣ k` and `n = m·c`, and produces `C(m, s+1)` bad challenges at
radius `n − k − c` with `k = c·s`. At the deployed row the radius constraint `n − k − c ≤ e`
forces `c ≥ w = 69632`, and `c ∣ 2²⁰` then forces `c ≥ 2¹⁷`; the largest admissible count is at
`c = 2¹⁷`, `s = 8`, `m = 16`. Formalised (with the block hypotheses explicit, using the new
radius-monotonicity `isBad_mono` / `card_badSet_mono`):

```lean
theorem deployed_block_pencil_lower_bound [Fintype F] (hD : D.card = 2097152)
    {O : Fin 16 → Finset ↥D} {b : Fin 16 → F}
    (hO : ∀ i, ∏ x ∈ O i, (X - C (x : F)) = X ^ 131072 - C (b i))
    (hdisj : ∀ i j : Fin 16, i ≠ j → Disjoint (O i) (O j))
    (hinj : ∀ I J : Finset (Fin 16), I.card = 9 → J.card = 9 →
      ∑ i ∈ I, b i = ∑ i ∈ J, b i → I = J) :
    11440 ≤ (badSet 1048576 978944
      (fun x : ↥D => (x : F) ^ 1179648) (fun x : ↥D => (x : F) ^ 1048576)).card
```

*Conditional* (on the block data existing over the deployed field, which is **not** constructed
here) and `C(16,9) = 11440 < B*` (`deployed_block_pencil_far_below_target`). Conclusion for the
counterexample route: the known structured families miss `B*` by a factor `> 2·10¹³` at this row,
so no `OFFICIAL_COUNTEREXAMPLE` is available from them; this is *not* evidence that the row is
safe.

### 6.3 Discipline checks

* No pivot-depth recurrence is used anywhere; the `(k,w) → (k+a,w−a)` residualisation does not
  appear (the code degree issue flagged in the mission is respected: no statement here changes
  `k`).
* The `m = 8` differential-trade identities (`P_A−P_B = cX`, `4P + c²X² = S²`, `P ∣ N²−(P′)²`) and
  the μ2/μ4/μ8 periodic cases do not appear.
* No disjointness, sunflower, Johnson, second-moment or raw support-counting step is used; the
  bridge and the obstruction are pure linear algebra plus the source adapters.
* No external census is imported; nothing from `Agent2`/`MathAgent`-style tabulations is cited.
* No `sorry`, no `admit`, no `native_decide`, no new `axiom`, no `@[implemented_by]`.

## 7. Build status and axioms

```
lake build RequestProject.Root.CodingTheory.GlobalChallengeAnnihilator
lake build RequestProject.Root.CodingTheory.GrandMcaGlobalGate
lake build RequestProject.GlobalChallengeAnnihilatorAxiomAudit
lake build RequestProject.GrandMcaGlobalGateAxiomAudit
```

all succeed (Lean 4.28.0, Mathlib `v4.28.0`). Every theorem listed in the two audit files reports

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`deployed_width` reports `[propext]` only). No file outside the four listed above was modified.

## 8. The single smallest remaining implication

> **Gate (deployed).** `DeployedSplitLocatorGate D`: for every official pair `(f₀,f₁)` on the
> deployed domain, `#{γ ∈ F : ∃ E ⊆ D, |E| = 978944, ∀ h with deg h < 69632,
> gsynd f₀ (Q_E·h) + γ·gsynd f₁ (Q_E·h) = 0, and gsynd f₁ (Q_E·h) ≠ 0 for some such h} ≤ B*`.

Given the gate, `#Bad ≤ B*` and `ε_mca^max ≤ B*/|K|` follow (proved, §4). Without additional
input about *split* locators the gate cannot be reached: by §5 the same set with "split `Q_E`"
relaxed to "nonzero `Q` of degree `≤ e`" is all of `F`. Any future attempt must therefore supply a
quantitative handle on

> how many distinct `γ` can have the `909313`-dimensional kernel `ker(A + γB) ⊆ F[X]_{≤e}` meet
> the finite set of monic degree-`e` polynomials split over `D`,

i.e. an intersection-theoretic or coding-theoretic bound for a linear space of codimension `w`
meeting the minimum-weight codewords of `RS_{e+1}(D)`. That is the whole remaining content of the
deployed row.
