# Generality extraction checkpoint

Written after Steps 1–4 of the Circle-FRI prover-word mission and **before** any further
Circle-STARK or capacity work (which is frozen).

The question: of everything used to prove the Circle-FRI prover-word lemma and the one-round
certificate, how much is about the circle, how much about the fold, how much about polynomials,
and how much is a single mechanism that would work for any code?

The answer, and it is now a Lean fact and not a slogan:
**the whole `#Bad ≤ 1` half is one mechanism, and the mechanism is a minimum-distance statement
about an ambient linear code.**  The circle contributes exactly one lemma (the prover-word
lemma), and polynomials contribute exactly one lemma (root counting).

---

## 1. The extracted generic theorem

In `RequestProject/Root/CodingTheory/ZeroLocusGeneral.lean`, for an arbitrary field `F`, an
arbitrary finite index type `ι` and an arbitrary `F`-module alphabet `A`:

```lean
def ZeroBounded (V : Submodule F (ι → A)) (t : ℕ) : Prop :=
  ∀ v ∈ V, v ≠ 0 → (agreementSet v (0 : ι → A)).card < t

theorem zeroBounded_iff_minDistGe {V : Submodule F (ι → A)} {t : ℕ} :
    ZeroBounded V t ↔ MinDistGe V (Fintype.card ι - t + 1)

theorem card_badSet_le_one_of_zeroBounded
    (hf₁ : f₁ ∉ C) (hCV : C ≤ V) (hf₁V : f₁ ∈ V) (hV : ZeroBounded V t)
    (ht : 2 * e + t ≤ Fintype.card ι) :
    (badSet C e f₀ f₁).card ≤ 1

theorem epsMCA_le_one_div_of_zeroBounded ... : epsMCA C e f₀ f₁ ≤ 1 / |F|
```

The "zero-locus structure" the mission asked for is therefore, concretely:

> **the tested second layer `f₁` and the whole tested code `C` sit inside one ambient linear
> code `V` whose minimum distance exceeds `|ι| − t`.**

`zeroBounded_iff_minDistGe` shows this is not a new notion at all: it is minimum distance, in a
form indexed by the zero-count parameter `t` instead of by the distance.  The `#Bad ≤ 1`
conclusion then follows with `2e + t ≤ |ι|` and nothing else — no polynomials, no evaluation
map, no geometry, no field structure on the alphabet.

**Verdict: the abstraction succeeded.**  All of Step 4 moved into the generic module; nothing
circle-specific blocks it.

## 2. The three instances, all proved through the generic theorem

| instance | ambient code `V` | zero-count parameter | source of `ZeroBounded` |
|---|---|---|---|
| ordinary Reed–Solomon | `reedSolomonCode F D t` | `t` | root counting (`zeroBounded_reedSolomonCode`) |
| circle code | `circleCode D t'` | `2t' + 1` | norm counting, needs `2 ≠ 0` (`zeroBounded_circleCode`) |
| Circle-FRI round, post-fold | `reedSolomonCode F (π D) t` | `t` | root counting again (`circle_fri_one_round_card_badSet_le_one_generic`) |
| folded Reed–Solomon (block alphabet `Fin s → F`) | `foldedRSCode B k' s γ` | any `t > ⌊(k'−1)/s⌋` | the folded minimum distance already in the project (`zeroBounded_foldedRSCode`) |

The fourth row is the abstraction test: a code with a *different alphabet* (blocks
`Fin s → F` rather than field elements), for which nothing new had to be proved — feeding the
existing minimum-distance bound `foldedRS_minDistGe` to the mechanism yields
`foldedRS_card_badSet_le_one` and `foldedRS_epsMCA_le_one_div` directly.  This is the strongest
available evidence that the mechanism is genuinely code-agnostic.

The *only* difference between the univariate and the circle certificate is the parameter that
the ambient code's minimum distance supplies: `t` versus `2t' + 1`.  The factor 2 is the circle
norm `a² − (1 − x²)b²` and it is the sole quantitative circle-specific ingredient anywhere in
the two certificates.

Note the third row: after the fold the instance is *univariate*, so the fold **buys back the
factor 2** — this is the concrete reason the one-round Circle-FRI certificate has the `2e + t`
bookkeeping while the direct circle certificate has `2e + 2t + 1`.

## 3. Classification of every fact used in Steps 3–4

### 3.1 Step 3 — the prover-word lemma (`circle_fold_snd_eq_eval_b`)

| fact | class | comment |
|---|---|---|
| `circleFoldInv p = p⁻¹`, `(J p).x = p.x`, `(J p).y = −p.y` | **fold-specific** | the only properties used are: `J` is an involution, fixes the projection, negates the second coordinate.  The circle group structure is *not* used — `J` could be any such involution. |
| `J` is an involution, fixed points are `y = 0` | **fold-specific** | recorded (`circleFoldInv_involutive`, `circleFoldInv_eq_self_iff`) but not needed by the lemma itself; it is what makes the section condition `(σ u).y ≠ 0` the right one. |
| `w(x, y) = a(x) + y·b(x)` (the two-term shape) | **circle-specific in appearance, fold-general in substance** | what is used is that the word lies in a free rank-2 module over the base ring with `J` acting as `+1` on the first summand and `−1` on the second.  This is the same structure as the radix-2 FRI split `f = f_even(x²) + x·f_odd(x²)` of `FRIFoldStructured.lean`, and the two proofs are line-for-line parallel. |
| `2 ≠ 0` | **general** | any fold that separates a `±1` eigendecomposition needs it.  Also independently necessary: in characteristic 2 the circle norm can vanish identically (recorded counterexample). |
| `(σ u).y ≠ 0` | **fold-specific** | `σ u` must not be a fixed point of `J`; otherwise the second layer is a `0/0` quotient and `b` is not determined by the word.  Verified numerically (test P4). |
| `(σ u).x = u`, `σ u ∈ D` | **fold-specific** | section of the projection. |
| `div_eq_iff`, `ring` | **formalisation artefact** | |
| `exists_circleFoldSection` (choice over fibres) | **formalisation artefact** | non-vacuity, uses `Classical.choose`. |

**Nothing in Step 3 is polynomial-evaluation-specific.**  The identity
`foldSnd (a + y·b) = b` is an identity of module components; `a` and `b` never need to be
polynomials for it.  They are polynomials only because Step 4 wants a degree.

### 3.2 Step 4 — the one-round certificate

| fact | class | comment |
|---|---|---|
| `Alphabet.card_badSet_le_one_of_zeroCount` | **zero-locus-general** | already generic before this mission (arbitrary code, arbitrary alphabet). |
| `Alphabet.card_badSet_le_one_of_zeroBounded` | **zero-locus-general** | new; the mechanism in its final form. |
| `zeroBounded_iff_minDistGe` | **zero-locus-general** | new; identifies the hypothesis as minimum distance. |
| root counting `card_roots_in_lt_of_degree_lt` | **polynomial-evaluation-specific** | the *only* polynomial input to the whole certificate.  Isolated in `zeroBounded_reedSolomonCode`. |
| circle norm count `card_circleZeros_le_two_mul` | **circle-specific** | the only circle input to the *direct* circle certificate; **not used at all** by the post-fold one-round certificate. |
| nesting `reedSolomonCode_mono`, `circleCode_mono` | **zero-locus-general** | needed to have one ambient `V ⊇ C`. |
| degree window `k ≤ deg b < t` | **polynomial-evaluation-specific** | in the generic form it becomes `f₁ ∉ C` and `f₁ ∈ V`; the degree window is one way to certify both. |
| `2e + t ≤ |ι|` | **zero-locus-general** | |
| `Fintype.card_coe`, `one_div_le_one_div_of_le`, `positivity` | **formalisation artefact** | |
| `badSet` (`MCA.lean`) vs `Alphabet.badSet` (`AlphabetMCA.lean`) | **formalisation artefact — now removed** | `badSet_eq_alphabet_badSet` proves the polynomial-existential and submodule-existential definitions describe the same finite set, and `epsMCA_eq_alphabet_epsMCA` the same for the probability.  Before this checkpoint the correspondence was only informal. |

## 4. What did *not* generalise, and why

1. **The derivation of `ZeroBounded` is genuinely per-code.**  The mechanism consumes a
   minimum-distance bound for the ambient code; it cannot produce one.  For Reed–Solomon it is
   root counting; for the circle code it is the norm count (with its `2 ≠ 0` hypothesis).  A
   new code needs exactly one new lemma, of the shape `ZeroBounded V t`, and gets the whole
   certificate for free.  This is the natural test for a further generalisation step.
2. **The prover-word lemma is fold-specific and does not follow from the mechanism.**  It is
   the statement that the protocol's second layer lands in the ambient code at all.  Every new
   fold needs its own version.  Two are now proved and they are parallel: `friSnd_eval` (radix-2
   univariate) and `circle_fold_snd_eq_eval_b` (circle inversion).
3. **The mechanism is confined to `2e + t ≤ |ι|`.**  This is a unique-decoding-radius
   condition; it says nothing at or beyond capacity, and no capacity claim is made or implied
   anywhere in this checkpoint.
4. **`f₁ ∉ C` is a real hypothesis, not a technicality.**  When `f₁ ∈ C` the bad set is empty
   (`badSet_eq_empty_of_snd_mem`), so the two regimes together are a dichotomy; but the
   mechanism itself gives nothing in the third regime `f₁ ∉ V`, where only the counting bound
   `#Bad ≤ e + 1` is available.

## 5. Consequence for the roadmap

The evidence for a universal mechanism is now strong and, more importantly, *checked*: three
different certificates factor through one generic theorem, and the only per-instance inputs are
(a) one minimum-distance lemma for the ambient code and (b) one prover-word lemma per fold.

The natural next probes, in order, are:

* ~~apply the mechanism to a third, structurally different code~~ — **done in this
  checkpoint**: the folded Reed–Solomon code, with a block alphabet, goes through unchanged;
* the **syndrome/MDS** route, as *diagnostics*: locate precisely where the mechanism stops
  giving anything, i.e. the largest `t` for which an ambient `V` with the required minimum
  distance exists;
* a **comparison with ordinary Reed–Solomon beyond unique decoding**, to see which of the four
  hypotheses (`f₁ ∉ C`, `f₁ ∈ V`, `ZeroBounded V t`, `2e + t ≤ |ι|`) is the first to fail.

No Circle-STARK library, no multi-round claim, no capacity claim is made here.
