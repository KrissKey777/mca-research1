# CORRELATED_COMMON_SUPPORT_GATE — report

**Mission.** Decide, before any `#Bad ≤ e` work in the correlated (`W_can = 0`) branch, whether
the *common support of size `≤ e`* is (A) already written into the existing correlated-agreement
definitions, (B) a consequence of already formalised lemmas, (C) a new lemma, (D) true only in a
weakened form, or (E) false.

**Verdict.** The question has a different answer for each of the three notions that exist in the
repository, and all four answers are now machine-checked, not argued on paper:

| # | notion actually present in the Lean sources | verdict |
|---|---|---|
| 1 | Reed–Solomon correlated agreement (`correlatedAgreement_of_card_goodZ_gt`, `correlatedAgreement_of_card_goodZ_gt_third`) | **A — already in the definition** |
| 2 | the downstream item that was blocked, `#Bad ≤ e` in the correlated branch | **B — consequence of already formalised lemmas** |
| 3 | abstract-alphabet `LineAgreeOn` | **C — new (small) lemma**, now proved |
| 4 | `SlackCorrelatedAgreement` | **D — true, but at radius `e + θ`, not `e`** |
| 5 | the reading "each coordinate separately `e`-close" | **E — false**, explicit counterexample |

Consequently: **the freeze can be lifted.** `#Bad ≤ e` in the correlated branch is not new
mathematics and needs no new theory; it is a two-line corollary, and it is proved below.

New Lean file: `RequestProject/Root/CodingTheory/CorrelatedCommonSupport.lean`
(built; `#print axioms` in `RequestProject/Main.lean` reports `[propext, Classical.choice,
Quot.sound]` for every declaration listed here; no `sorry`, no new axiom).

---

## 1. What is actually in the repository

There is **no** declaration literally named `CorrelatedAgreementAtRadius`. The correlated-agreement
content of the project sits in three places, with three different shapes:

1. **Reed–Solomon layer** (`CorrelatedAgreement.lean`, `CorrelatedAgreementRefined.lean`). The
   conclusion of both correlated-agreement theorems is

   ```
   ∃ q₀ q₁ : F[X], deg q₀ < k ∧ deg q₁ < k ∧
     D.card ≤ (polyAgreement f₀ q₀ ∩ polyAgreement f₁ q₁).card + e
   ```

   i.e. a bound on the *complement* of one common agreement set.

2. **Abstract-alphabet layer** (`AlphabetMCA.lean`): `LineAgreeOn C S f₀ f₁ := ∀ γ, AgreeOn C S
   (lineComb f₀ f₁ γ)` — every point of the line agrees with *some* codeword on the same `S`. No
   pair `(c₀,c₁)` is exhibited.

3. **Slack layer** (`SharpLineMCA.lean`): `SlackCorrelatedAgreement C e θ err` — either
   `∃ T, |ι| ≤ |T| + e + θ ∧ LineAgreeOn C T u₀ u₁`, or the probabilistic alternative.

The `W_can = 0` branch of `SubresultantCore.lean` contains no correlated-agreement definition at
all (`rg -i correlated` on that file returns nothing), which is exactly why the question was open:
the notion used in the paper-level `W_can = 0` reports is notion 1, imported from the RS layer.

## 2. Verdict A — the RS notion *is* the common support

`commonErrorSupport f₀ f₁ q₀ q₁ := (polyAgreement f₀ q₀ ∩ polyAgreement f₁ q₁)ᶜ` is the set of
positions where at least one coordinate deviates. The two readings are equal by counting:

* `card_commonErrorSupport` : `|E| + |T| = |D|`;
* `commonErrorSupport_card_le_iff` : `|E| ≤ e ↔ |D| ≤ |T| + e`;
* `exists_commonErrorSupport_of_correlatedAgreement` : correlated agreement ⟹
  `∃ E, |E| ≤ e ∧ ∀ x ∉ E, f₀ x = q₀(x) ∧ f₁ x = q₁(x)`;
* `correlatedAgreement_of_commonErrorSupport` : the converse.

So the normal form `f₀ = p₀ + a`, `f₁ = p₁ + b` with one shared error set `E`, `|E| ≤ e`, used in
the paper-level `W_can = 0` analysis, is **the definition unfolded**, not an extra hypothesis and
not an extra theorem. Nothing about `W_can`, subresultants, unique decoding or the window
`k + 2e ≤ n` is needed for this step; it is pure complementation.

## 3. Verdict B — `#Bad ≤ e` in the correlated branch is already implied

`card_badSet_le_card_compl` (already in `CorrelatedAgreementRefined.lean`, kernel-checked) says:
given correlated agreement on `T` and `1 ≤ k`, `k ≤ |D|`, `2e + k ≤ |D|`,

```
#Bad ≤ |D| − |T| .
```

Combined with §2 this is literally `#Bad ≤ |E|`. Hence, newly recorded in Lean:

* `card_badSet_le_card_commonErrorSupport` : `#Bad ≤ |commonErrorSupport f₀ f₁ q₀ q₁|`;
* `card_badSet_le_of_correlatedAgreement` : with `1 ≤ k` and `k + 2e ≤ |D|`, correlated agreement at
  radius `e` gives **`#Bad ≤ e`**;
* `card_badSet_le_of_card_goodZ_gt_third` : with `1 ≤ k`, `k + 3e ≤ |D|` and more than `2e + 1` good
  challenges, `#Bad ≤ e`.

Two remarks on how this sits with what was already there.

* The existing `card_badSet_le_third` gives `#Bad ≤ 2e + 1` under `k + 3e ≤ |D|`. That constant is
  **not** the cost of the correlated branch: its proof splits into "few good challenges"
  (`#Bad ≤ #Good ≤ 2e + 1`) and "correlated agreement", and the second half already yields `e`. So
  `2e + 1` is paid entirely by the *other* branch, and inside the correlated branch the sharp
  constant is `e`.
* The window used is `k + 2e ≤ |D|` (`hkD` and `h2e` of `card_badSet_le_card_compl` follow from it),
  matching the window in which the `W_can` machinery is stated. No hypothesis about `W_can ≠ 0`,
  the kernel, `ν`, or the algebraic closure enters.

Therefore the item the mission suspended — "do not formalise `#Bad ≤ e` in the correlated branch
until the support question is settled" — is settled in the cheapest possible way: the bound holds,
its proof is three lines on top of existing lemmas, and it is now in the build.

## 4. Verdict C — the abstract notion needs one small lemma

`LineAgreeOn C S f₀ f₁` quantifies over the line and produces a codeword per point; it does not
name a pair. Evaluating at `γ = 0` and `γ = 1` and subtracting gives one:

* `Alphabet.exists_agree_pair_of_lineAgreeOn` : `LineAgreeOn C S f₀ f₁ ⟹ ∃ c₀ ∈ C, ∃ c₁ ∈ C`,
  `f₀ = c₀` on `S` and `f₁ = c₁` on `S`. (Uses only that `C` is a submodule; `c₁ := c − c₀`.)
* `Alphabet.exists_commonErrorSupport_of_lineAgreeOn` : with `|ι| ≤ |S| + m`, this gives a common
  error support of size `≤ m`.

This is a genuine lemma rather than an unfolding, but a four-line one; it does not carry
mathematical risk. It matters only because it is the step that converts the abstract notion into
the normal form used in the `W_can` discussion.

## 5. Verdict D — the slack notion has radius `e + θ`

`Alphabet.exists_commonErrorSupport_of_slack` : when the probabilistic alternative of
`SlackCorrelatedAgreement C e θ err` fails, one obtains a common error support of size **`e + θ`**.
The `θ` cannot be removed: it is introduced in `card_inter_agreement_ge_of_collinear_slack` and paid
for by the hypothesis `e ≤ (b−1)·θ` of `slackCorrelatedAgreement_of_lineDecodable`. Any downstream
statement that cites *this* notion and then claims a support (or a `#Bad`) bound of `e` is off by
`θ`. Since the folded-RS results (`FoldedRSSharp.lean`) go through the slack notion, this is the
one place where the naive transfer would be wrong.

## 6. Verdict E — what is false

The tempting reading "`f₀` and `f₁` are each `e`-close, hence they have a common error support of
size `≤ e`" is false, and `separate_closeness_not_common_support` records a minimal counterexample,
checked by `decide`: over `𝔽₅` with `n = 5` positions, the constant code (`k = 1`) and `e = 1`, take
`f₀ = δ₀` and `f₁ = δ₁`. Each is at distance `1` from the zero codeword, yet for *every* pair of
constants `(a,b)` the common agreement set has at most `3` positions, i.e. `< n − e = 4`. The
correlation is essential; only the correlated statement (notion 1) delivers a common support.

## 7. Consequences for the next step

1. `#Bad ≤ e` in the correlated branch: **done**, in the build, no new theory, window `k + 2e ≤ n`.
   The paper-level claim `#Bad ≤ |E| ≤ e` of the `W_can = 0` analysis is confirmed in its counting
   part; what is *not* covered by the present file is the algebraic characterisation
   `Bad = {−a(x)/b(x) : x ∈ E, b(x) ≠ 0}` (equality, not just the bound), which remains a paper
   result and a legitimate next formalisation target.
2. The route `W_can = 0 ⇒ correlated agreement at radius e` itself is still unformalised — it is the
   only remaining gap between `SubresultantCore.lean` and `card_badSet_le_of_correlatedAgreement`.
   Once it exists, the two branches compose to an unconditional statement with no `W_can ≠ 0`
   hypothesis.
3. When quoting a support radius, always say which notion: `e` for the RS notion, `e + θ` for the
   slack notion, and never a per-coordinate radius (§6).

## 8. Declarations added

`RequestProject/Root/CodingTheory/CorrelatedCommonSupport.lean`:

```
Root.CodingTheory.commonErrorSupport                              (definition)
Root.CodingTheory.mem_commonErrorSupport
Root.CodingTheory.eq_of_notMem_commonErrorSupport
Root.CodingTheory.card_commonErrorSupport
Root.CodingTheory.commonErrorSupport_card_le_iff                  (verdict A)
Root.CodingTheory.exists_commonErrorSupport_of_correlatedAgreement(verdict A)
Root.CodingTheory.correlatedAgreement_of_commonErrorSupport       (verdict A, converse)
Root.CodingTheory.card_badSet_le_card_commonErrorSupport          (verdict B)
Root.CodingTheory.card_badSet_le_of_correlatedAgreement           (verdict B, #Bad ≤ e)
Root.CodingTheory.card_badSet_le_of_card_goodZ_gt_third           (verdict B, chained)
Root.CodingTheory.separate_closeness_not_common_support           (verdict E)
Root.CodingTheory.Alphabet.exists_agree_pair_of_lineAgreeOn       (verdict C)
Root.CodingTheory.Alphabet.exists_commonErrorSupport_of_lineAgreeOn
Root.CodingTheory.Alphabet.exists_commonErrorSupport_of_slack     (verdict D, radius e + θ)
```
