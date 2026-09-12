# Circle ↔ `StructuredSecondLayer` bridge — semantic audit (PHASE 0)

*Purpose.*  Before any circle statement is attempted, record **exactly** what the proved
theorem `Root.CodingTheory.card_badSet_le_one_of_structured_snd` says, which hypothesis of it
carries the proof, and in which of the three possible ambient structures

* `F[X]` — ordinary polynomial evaluation,
* `F[X]²` — a rank-two module over `F[X]`,
* `F[X,Y]/(Y² − (1 − X²))` — the circle quotient ring,

a *circle word* actually lives.  Nothing is assumed here; every claim below is either quoted
from the repository or marked as an obligation to be settled by the Phase 1 experiment.

This file is written before any circle code is added to the aggregator, as instructed.

---

## 1. The strong MCA / `Bad` definition used by `StructuredSecondLayer`

Verbatim from `RequestProject/Root/CodingTheory/MCA.lean` (unchanged, on the freeze list):

```lean
def IsCloseOn (k : ℕ) (S : Finset ↥D) (f : ↥D → F) : Prop :=
  ∃ p : F[X], p.degree < (k : WithBot ℕ) ∧ ∀ x ∈ S, f x = p.eval (x : F)

def LineCloseOn (k : ℕ) (S : Finset ↥D) (f₀ f₁ : ↥D → F) : Prop :=
  ∀ γ : F, IsCloseOn k S (lineComb f₀ f₁ γ)

def IsBad (k e : ℕ) (f₀ f₁ : ↥D → F) (γ : F) : Prop :=
  ∃ S : Finset ↥D, D.card ≤ S.card + e ∧ IsCloseOn k S (lineComb f₀ f₁ γ) ∧
    ¬ LineCloseOn k S f₀ f₁

noncomputable def badSet (k e : ℕ) (f₀ f₁ : ↥D → F) : Finset F :=
  Finset.univ.filter (IsBad k e f₀ f₁)
```

This is the **strong** definition: the witness set `S` is existentially quantified *per
challenge* `γ`, and badness means the *same* `S` fails for the whole line.  It is strictly
stronger (larger bad set) than the "slack" variants; it is frozen and is not touched anywhere
below.

The alphabet-generic mirror in `RequestProject/Root/CodingTheory/AlphabetMCA.lean`
(`Root.CodingTheory.Alphabet.IsBad`, `…badSet`) is the *same* definition with
`IsCloseOn k S f` replaced by `AgreeOn C S f := ∃ c ∈ C, ∀ x ∈ S, f x = c x` for an arbitrary
`C : Submodule F (ι → A)`.  For `C = {evaluations of polynomials of degree < k}` and `A = F`
the two coincide definitionally up to the description of the code.  **This is the only place
where the bridge may attach without touching the frozen definition.**

## 2. The fold map, and the meaning of "first" and "second layer"

`RequestProject/Root/CodingTheory/FRIFoldStructured.lean`, for the *univariate* radix-2 fold,
with a square-root section `σ : ↥D → F` of the folded domain (`(σ y)² = y`, `σ y ≠ 0`):

```lean
def friFst (f : F → F) (σ : ↥D → F) : ↥D → F := fun y => (f (σ y) + f (-(σ y))) / 2
def friSnd (f : F → F) (σ : ↥D → F) : ↥D → F := fun y => (f (σ y) - f (-(σ y))) / (2 * σ y)
```

so the layers are the even/odd parts with respect to the involution `x ↦ −x` of the pre-fold
domain, read on the folded domain `D = {x²}`.  The MCA line that FRI actually tests is
`γ ↦ friFst + γ · friSnd` **on the folded domain**, against the folded code
(`degree < k`, where the pre-fold bound is `2k`).

`friSnd_eval` proves: if the tested word is `x ↦ P.eval x` then `friSnd = eval (oddPart P)`.
So for the univariate fold the second layer *is* an ordinary polynomial evaluation — proved,
not assumed.

**Circle analogue (the object under audit).**  The circle group of `CircleGroup.lean` is

```lean
structure Circle (F) where x : F ; y : F ; norm_one : x ^ 2 + y ^ 2 = 1
```

with inverse `(x, y)⁻¹ = (x, −y)`.  Inversion is therefore exactly the involution `J` that
fixes the `x`-coordinate, and the analogue of the radix-2 fold is the **`J`-fold** (the
"circle-to-line" step of Circle-FRI): for a word `w : ↥D → F` on a `J`-stable circle domain
`D` with `y ≠ 0` everywhere,

```
w₀(x) = (w(x, y) + w(x, −y)) / 2 ,      w₁(x) = (w(x, y) − w(x, −y)) / (2y)
```

read on the projected domain `S = π_x(D) ⊆ F`, `|S| = |D|/2`.  Both are functions on `S`; the
line tested after one circle round is `γ ↦ w₀ + γ · w₁` **on `S`**.

## 3. The evaluation domain and the `x`-projection

`RequestProject/CircleFFT.lean` uses the twin coset

```
cpt q m i = q^(4i+1)                    (i < 2^m)
cpt q m i = (q^(4(i−2^m)+1))⁻¹          (2^m ≤ i < 2^(m+1))
```

i.e. `D = q·H ∪ q⁻¹·H` with `H = ⟨q⁴⟩`, `|D| = 2^(m+1)`.  Two structural facts matter:

* `D` is **stable under inversion** `J : p ↦ p⁻¹ = (p.x, −p.y)`, because the two halves are
  exactly each other's inverses;
* consequently `π_x : D → F`, `p ↦ p.x`, is **2-to-1** onto a set `S` of size `|D|/2`, provided
  no point of `D` has `y = 0` (equivalently `p ≠ p⁻¹`, i.e. `p` is not of order ≤ 2).

Neither fact is currently proved in the repository; both are obligations for any bridge that
uses the projection (obligation **O3** below).

## 4. What *is* a circle word?  (the question that must be settled first)

The Circle-FFT space of `CircleFFT.lean` is spanned by products of the twiddle tower
`v₀ = x`, `v_{j+1} = 2v_j² − 1` together with the single factor `y`.  Since
`{∏ v_j^{e_j} : e ∈ {0,1}^m}` spans exactly the polynomials in `x` of degree `< 2^m`, the
span of the CFFT basis is

```
C_k(D) = { p ↦ a(p.x) + p.y · b(p.x)  :  deg a < k, deg b < k }        (†)
```

which is the image of `F[X, Y]/(Y² − (1 − X²))` — the coordinate ring of the circle, since
`x² + y² = 1` — restricted to degrees `< k` in each of the two `F[X]`-module components.

So the honest classification is:

| candidate | verdict |
|---|---|
| ordinary polynomial evaluation `g(x)` | **no** — a circle word is *not* a function of `x` alone unless `b = 0`; it is 2-valued on each `x`-fibre |
| module evaluation (rank-two `F[X]`-module `F[X] ⊕ y·F[X]`) | **yes**, and this is the same thing as |
| quotient-ring evaluation `F[X,Y]/(Y² − (1 − X²))` | **yes** (the quotient ring *is* the free rank-two module `F[X] ⊕ y·F[X]`, since `Y² − (1−X²)` is monic of degree 2 in `Y`) |
| a sum of components | yes in the trivial sense `a + y·b`; the components are not separately words on `D` |

Phase 1 must exhibit the first counterexample to "circle word ⇒ ordinary polynomial
evaluation" explicitly rather than relying on the argument above.

**But the layer is a different object from the word.**  Applying the `J`-fold of §2 to a word
of the form (†) gives `w₀ = a|_S`, `w₁ = b|_S`: the second layer of a circle word **is** an
ordinary polynomial evaluation on `S`.  The two statements are compatible and it is essential
not to confuse them.  Both are tested in Phase 1.

## 5. The exact degree/zero-count condition the existing proof uses

The proof of `card_badSet_le_one_of_structured_snd` (reproduced from the source) is:

1. two distinct bad `γ, γ'` are both close to the code;
2. `correlated_agreement_of_two` produces codewords `q₀, q₁` (degree `< k`) and a set `T` with
   `|T| ≥ |D| − 2e ≥ t` on which `f₀ = q₀` and `f₁ = q₁`;
3. `g − q₁` has degree `< t` and vanishes on `T`, `|T| ≥ t`, hence `g − q₁ = 0`;
4. hence `deg g = deg q₁ < k`, contradicting `k ≤ deg g`.

Step 3 is the **only** place where anything about polynomials is used, and it is used only as:

> a nonzero element of `span(code ∪ {f₁})` has **fewer than `t` zeros on `D`**.

Step 4 is used only as:

> `f₁` is **not** a codeword.

Everything else (steps 1, 2) is already alphabet- and code-generic in `AlphabetMCA.lean`
(`Alphabet.correlatedAgreement_of_two` needs only that `C` is a submodule).  Therefore the
theorem's real content is

> **(Z)** if `f₁ ∉ C` and for every `c ∈ C` the difference `f₁ − c` agrees with `0` on fewer
> than `t` positions, and `2e + t ≤ n`, then `#Bad ≤ 1`.

No minimum distance, no `3e < d`, no Reed–Solomon structure is needed.  This is the
*zero-count* formulation (route **C** of the mission), and the audit's finding is that the
existing proof does support it — this is checked, not assumed, in Phase 1 (test T4) and then
proved in Lean.

## 6. Hypotheses required to instantiate the theorem, as obligations

| id | obligation | needed by route |
|---|---|---|
| **O1** | `C` is an `F`-submodule of `↥D → F` | A, B, C |
| **O2** | `f₁ ∉ C` (the second layer is not itself a codeword) | A, B, C |
| **O3** | `D` stable under `J`, `y ≠ 0` on `D`, `π_x` 2-to-1 onto `S` | A only (fold route) |
| **O4** | `char F ≠ 2` (division by `2` and `2y`; also `1 − X²` must not be a square) | A, B, C |
| **O5** | zero-count: a nonzero `a(x) + y·b(x)` with `deg a, deg b < t'` has `< t` zeros on `D` | C |
| **O6** | degree window `k ≤ deg g < t` for the second layer `g` | A |
| **O7** | `2e + t ≤ |D|` (route C) resp. `2e + t ≤ |S| = |D|/2` (route A) | A, C |

`O5` has an expected value: with `N(x) := a(x)² − (1 − x²) b(x)²` (the norm of `a + yb` for the
quadratic extension `F[X][Y]/(Y² − (1 − X²))`),

* `N ≠ 0` whenever `(a, b) ≠ (0, 0)`, because `1 − X²` is squarefree of degree 2, hence not a
  square in `F[X]` — **fails in characteristic 2**, where `1 − X² = (1 + X)²`;
* every zero of `a + yb` on `D` projects to a zero of `N`, and an `x`-fibre contributing *two*
  zeros forces `a(x) = b(x) = 0`, i.e. a **double** root of `N`;
* hence `#zeros_D(a + yb) ≤ deg N ≤ max(2 deg a, 2 deg b + 2) ≤ 2t'` for `deg a, deg b < t'`.

Phase 1 must test this bound, its tightness, and the characteristic-2 failure.

## 7. What Phase 1 must falsify

```
(i)   circle word              ⇒  ordinary polynomial evaluation on D
(ii)  minimum distance of C_k  ⇒  hypotheses of StructuredSecondLayer
(iii) module-degree window     ⇒  #Bad ≤ 1
(iv)  one circle round         ⇒  the *same* strong MCA quantity as the univariate theorem
```

with separating examples, not aggregate maxima.  Only after that is a route chosen.

## 8. Phase 1 — outcome of the exact falsification experiment

`analysis/circle_bridge_falsification.py` (exact integer arithmetic, output saved as
`analysis/circle_bridge_falsification_output.txt`).

| test | question | verdict |
|---|---|---|
| T1 | circle word ⇒ ordinary polynomial evaluation on `D` | **FALSE**, 172/172; first counterexample `q = 7`, `D = {(2,2),(5,5),(2,5),(5,2)}`, `a = 4`, `b = 6`, word `(2,6,6,2)` |
| T2 | `J`-folded second layer of a circle word = the ordinary polynomial `b` on `S` | **TRUE**, 0 failures in 172 |
| T3 | `#zeros_D(a + yb) ≤ deg N ≤ 2t'` | **TRUE**, 6 448 words, 0 violations, 12 attain `2t'` |
| T3b | the same in characteristic 2 | **FALSE**: over `F₂`, `a = 1 + X`, `b = 1` is nonzero, its norm is identically `0`, and the word vanishes on the whole circle |
| T4 | module-degree window ⇒ `#Bad ≤ 1` (circle code, strong bad set) | **TRUE** inside `2e + 2t' + 1 ≤ |D|`: 176 instances, max `#Bad = 1` (96 attain 1); control without the window reaches `#Bad = 3` |
| T5 | minimum distance ⇒ structured-layer conclusion | **FALSE**; first counterexample `q = 31`, `|D| = 8`, `k = 2`, `d = 4`, `e = 1` (so `3e < d`), `#Bad = 2` |
| T6 | one circle round ⇒ the *same* strong MCA quantity as the folded univariate instance | **FALSE**; 35 of 80 differ, separating examples in *both* directions (`#Bad(folded) = 1` vs `#Bad(circle) = 0`, and `1` vs `2`) |
| T7 | does the conclusion need a twin coset / `J`-stability / complete fibres? | **no**: 398 instances on arbitrary circle domains (115 with a point at `y = 0`, 199 with an incomplete fibre), max `#Bad = 1` |
| boundary | `2e + 2t' = |D|`, one short of the hypothesis | `#Bad = 2`: `q = 31`, `k = 2`, `t' = 3`, `e = 1`, `a = 18 + 19X + 3X²`, `b = 24 + 18X + 5X²`, bad set `{0, 19}` |

## 9. Phase 2 — the bridge chosen

**Route C (abstract zero count).**  §5 shows the existing proof uses only `f₁ ∉ C` and a bound
on the number of positions where a nonzero difference vanishes; the experiment (T4) confirms
the resulting statement and (T5) confirms that the weaker distance hypothesis does not suffice.
Route A is *refuted at the level of the circle code* (T1) and, although it holds after the fold
(T2), T6 shows the folded instance is a different MCA quantity, so it would not certify the
circle code.  Route B is subsumed: the rank-two module structure enters only through the zero
count, which is exactly what route C abstracts.

## 10. Phase 3 — what was formalized (and nothing more)

1. the abstract lemma — `Root.CodingTheory.Alphabet.card_badSet_le_one_of_zeroCount` and
   `…epsMCA_le_one_div_of_zeroCount`, plus the empty regime `…badSet_eq_empty_of_snd_mem`
   (`RequestProject/Root/CodingTheory/ZeroCountSecondLayer.lean`);
2. the circle bridge — `circleCode`, `circleNorm_ne_zero`, `card_circleZeros_le`,
   `circleWord_notMem_circleCode`, `zeroCountLt_circleWord`, `card_badSet_circle_le_one`
   (`RequestProject/Root/CodingTheory/CircleZeroCount.lean`);
3. one parameter certificate — `circle_epsMCA_le_two_pow_neg_128`.

No circle-code library, no Circle-STARK soundness claim, no multi-round statement.  All new
declarations are audited in `RequestProject/Main.lean` with `#print axioms`, each reporting only
`[propext, Classical.choice, Quot.sound]`.

## 11. Phase 4 — boundary checks

| boundary | outcome |
|---|---|
| `deg g = k − 1` (univariate, below window) | `#Bad = 0` in 656 instances — the empty regime |
| `deg g = k` (lower edge, inside) | max `#Bad = 8` *when the other hypotheses are relaxed*; inside the full window the scans give `≤ 1` |
| `deg g = t − 1` (upper edge, inside) | max `#Bad = 1` |
| `deg g = t` (above window) | max `#Bad = 8` — the window is essential |
| `2e + t = |D|` vs `|D| + 1` (univariate) | `≤ 1` vs max `#Bad = 7` |
| `2e + 2t' = |D|` (circle) | `#Bad = 2` — the `+1` slack is necessary |
| characteristic 2 | zero count fails outright; excluded by hypothesis |
| points with `y = 0`, incomplete/overlapping fibres, non-coset domains | harmless — the proved theorem never assumes anything about `D` (T7) |
| strong MCA definition | unchanged; the bridge attaches to `Alphabet.badSet`, which mirrors it verbatim |

## 12. Phase 5 — the reusable theorem

The zero-count formulation is valid, so the most general statement the proof justifies is
recorded as the primary theorem:

> for a linear code `C : Submodule F (ι → A)` (any alphabet, any index type) and a line
> `γ ↦ f₀ + γ·f₁`: if `f₁ ∉ C`, every codeword agrees with `f₁` in fewer than `t` positions,
> and `2e + t ≤ n`, then at most one challenge is bad, and `ε_mca ≤ 1/|F|`.

The Reed–Solomon statement of `StructuredSecondLayer.lean` and the circle statement of
`CircleZeroCount.lean` are the two instances: in the first the zero count comes from the degree
of a univariate polynomial, in the second from the degree of the norm
`a² − (1 − X²)b²` of a rank-two module element.

## 13. Status

Phases 0–5 complete.  Exactly one bridge proved; two rejected with explicit counterexamples.
