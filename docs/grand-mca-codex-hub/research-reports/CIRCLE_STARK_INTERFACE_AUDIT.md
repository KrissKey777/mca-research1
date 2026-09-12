# Circle-STARK / FRI interface audit (PHASE 3)

*Status: static audit of the repository as it stands. No new theorem is claimed here; the
purpose is to say precisely what would have to be built for the MCA results of
`RequestProject/Root/CodingTheory/` to apply to the Circle-FFT development of
`RequestProject/Circle*.lean`.*

## 1. What the repository actually contains

### 1.1 The circle side

| file | content |
|---|---|
| `RequestProject/CircleGroup.lean` | the circle group `Circle F = {(x,y) : x² + y² = 1}` with its group law; cyclicity over `M31` |
| `RequestProject/CircleFFT.lean` | the **twin-coset domain** `cpt q m i` and the twiddle tower `circleTw`, the radix-2 circle FFT and its correctness |
| `RequestProject/CircleLog.lean`, `FreeTwiddles.lean`, `MachineButterfly.lean`, `Reference.lean` | supporting material, machine-level butterflies, reference vectors |

The evaluation domain is

```
cpt q m i = q^(4i+1)          for i < 2^m
cpt q m i = (q^(4(i−2^m)+1))⁻¹ for 2^m ≤ i < 2^(m+1)
```

i.e. `D = q·H ∪ q⁻¹·H` with `H = ⟨q⁴⟩` of order `2^m`, and `|D| = 2^(m+1)`.

**So the circle domain is a union of exactly two cosets of a cyclic subgroup** — of the circle
group, not of `F^*`.

### 1.2 The coding-theory side

`RequestProject/Root/CodingTheory/` (≈100 files) develops mutual correlated agreement (MCA)
for **ordinary Reed–Solomon codes**: a domain `D : Finset F` of *field* elements, and
`IsCloseOn k S f` = "some univariate polynomial of degree `< k` equals `f` on `S`"
(`MCA.lean`).

### 1.3 The gap

```
$ rg -l "Circle" RequestProject/Root/CodingTheory/     # → no matches
```

The two developments are **completely disjoint**. There is at present no definition in the
repository of a circle code, of the circle FRI folding as a code map, or of a proximity
statement for circle codes.

## 2. Is the relevant packet monomial?

For the univariate MCA machinery a "packet" is a pair `(f₀, f₁)` of words on `D`, and the
monomial case means `f₀(t) = α t^{d₀}`, `f₁(t) = β t^{d₁}`.

* On the circle, the analogue of a monomial is a **character** `p ↦ p^d` composed with a
  coordinate, i.e. `Re(p^d)` or `Im(p^d)`. The FFT twiddles of `CircleFFT.lean` are exactly of
  this shape: `circleTw q m k i = (q^(2^{m−k−1}(4i+1))).x`.
* But those are the *twiddles*, not the words fed to a proximity test. The words that a FRI
  proximity gap statement quantifies over are arbitrary elements of the ambient space; only
  the *domain* and the *code* are structured.

**Conclusion.** The monomial hypothesis is a hypothesis on the packet, and the circle protocol
does not restrict the packet — it restricts the code. So a monomial-packet theorem, even a
proved one, does not by itself yield a Circle-STARK certificate. What the circle protocol does
supply is the domain structure (two cosets), which is the hypothesis on the *domain* side.

## 3. The numerical evidence that is relevant to the circle domain

`analysis/multicoset_monomial_scan.py` (exhaustive, exact arithmetic, 2 115 325 instances) in
the regime `3e + k ≤ |D|`:

| domain | instances | max `#Bad` |
|---|---:|---:|
| one coset `H` | 14 167 | 1 |
| one coset, degenerate coefficients | 3 881 | 1 |
| two cosets `H ∪ cH` | 251 786 | 1 |
| three cosets `H ∪ cH ∪ c'H` | 1 849 491 | **3** |

The sensitivity control `analysis/multicoset_monomial_control.py` shows that the same engine
does see `#Bad = 2` for *general* packets on the very same domains, so the ceiling of `1` in
the first three rows is a property of monomial packets, not an artefact.

The three-coset failure is formalized: `RequestProject/Root/CodingTheory/MulticosetMonomialWitness.lean`
(`ZMod 13`, `D = {±1, ±2, ±3}`, `k = 2`, `e = 1`, `f₀ = t⁴`, `f₁ = t⁵`, `#Bad = 2`).

Since the circle domain is a union of **two** cosets, it sits in the range where the scans
found no violation of `#Bad ≤ 1` — but see §4 for why that is not yet usable.

## 4. What would be needed for an application theorem

1. **A circle code definition.** A `Finset (Circle F)` domain plus the space of functions
   obtained by evaluating the quotient ring `F[x,y]/(x²+y²−1)` in degrees `< k`. Nothing of
   this exists in the repository.
2. **A bridge to univariate RS.** The standard route: the `x`-projection maps the twin coset
   2-to-1 onto a set of `2^m` field elements; a circle code splits into an even part and an
   odd part, each an RS-type code on the projected domain. Formalizing that splitting is the
   single largest missing piece, and it is what would let `MCA.lean` be applied at all.
3. **A statement of the FRI packet.** The pair `(f₀, f₁)` tested at a given folding round, in
   terms of the definitions of `CircleFFT.lean`.
4. **Only then** a certificate of the shape
   `ε_mca(circle code, δ) ≤ B/|K|`, with `B` coming either from the counting route
   (`card_badSet_le_succ_radius`, regime `3e < |D| − k + 1`) or from the circuit route
   (`CircuitIncidence.lean`).

## 5. Recommended interface (the theorem shape to aim for)

```lean
-- to be built: circle code and its bad set
def circleRS (D : Finset (Circle F)) (k : ℕ) : Set (↥D → F) := …
def circleBadSet (k e : ℕ) (f₀ f₁ : ↥D → F) : Finset F := …

-- the bridge
theorem circle_badSet_le_projected_badSet … :
    (circleBadSet k e f₀ f₁).card ≤ (badSet k' e' g₀ g₁).card

-- the certificate, obtained from the univariate results already proved
theorem circle_epsMCA_le … : epsMCAcircle k e D ≤ (B : ℝ) / Fintype.card F
```

Until step 2 exists, any claim of a Circle-STARK MCA certificate in this repository would be
unsupported. This audit records that honestly rather than asserting an application.

---

## 6. Re-audit after the structured-second-layer theorem (interface test)

The question this section answers, from the current mission: *in the concrete protocol, is
`f₁` the evaluation of a single polynomial `g`, what is `deg g`, and does it satisfy
`k ≤ deg g < t` with `2e + t ≤ |D|`?*

### 6.1 Univariate FRI — answered, and the certificate applies

`RequestProject/Root/CodingTheory/FRIFoldStructured.lean` now defines the radix-2 fold inside
the coding-theory development, so the question has a proved answer rather than a guess.

1. **Is `f₁` a single polynomial?**  Yes, *provided the tested word is*.  If the word is
   `x ↦ P.eval x`, then `friSnd` — the odd layer `(f(σy) − f(−σy))/(2σy)` — equals the
   evaluation of `oddPart P`, whose coefficients are the odd-indexed coefficients of `P`
   (`friSnd_eval`).  This is a theorem about the fold, not an assumption about the layer.
2. **What is `deg g`?**  `deg (oddPart P) = ⌊(deg P − 1)/2⌋`; exactly `m` when `deg P = 2m+1`
   (`degree_oddPart_eq_of_natDegree`), and `< n` whenever `deg P < 2n` (`degree_oddPart_lt`).
3. **Is the window met?**  `k ≤ deg g < t` holds precisely when `2k + 1 ≤ deg P ≤ 2t − 1`
   (taking `deg P` odd for the exact degree); `2e + t ≤ |D|` is a condition on the folded
   domain and the radius, met e.g. by `|D| = 2²⁰`, `k = 2¹⁹`, `t = k+1`, `e = 262143`.
4. **Instantiation.**  `fri_round_epsMCA_le_two_pow_neg_128`: with those parameters and a
   prover's word of degree `2²⁰ + 1` (one above the pre-fold bound `2k`),
   `ε_mca(line) ≤ 2⁻¹²⁸` for `|F| ≥ 2¹²⁸`, independently of the first layer.
5. **What fails.**  Nothing in the degree bookkeeping; the restriction is that the *word* be a
   polynomial evaluation.  For an arbitrary adversarial vector the hypothesis of
   `card_badSet_le_one_of_structured_snd` is simply not available and only `#Bad ≤ e + 1`
   applies.

### 6.2 Circle-STARK — still not applicable, and the exact failing condition

The failing condition is **not** one of `k ≤ deg g`, `deg g < t`, `2e + t ≤ |D|`.  It is prior
to all three: the repository has no circle code, hence no circle bad set, hence no `ε_mca` to
bound.  §§1–5 above list the missing structure; in the language of §6.1 the minimal missing
piece is

* the circle code on a twin-coset domain, and
* the identification of the circle fold's second layer with the odd part of the `x`-projection,

after which §6.1 transfers verbatim.  Until then the honest statement is the one made in §4:
no Circle-STARK certificate is claimed.

---

## 7. Feasibility probe (session closure): how large is the missing definition?

The closing question for this phase was narrow and is answered here so that it does not have
to be re-asked: *can the circle code be defined in this repository in 15–20 lines?*

**Interface: yes.**  On top of the existing `FFT.Circle` structure, the code on a domain
`D : Finset (Circle F)` is

```lean
noncomputable def circleRS (D : Finset (Circle F)) (k : ℕ) : Submodule F (↥D → F) :=
  Submodule.span F
    { f : ↥D → F | ∃ a b : Polynomial F, a.natDegree < k ∧ b.natDegree < k ∧
        ∀ p : ↥D, f p = a.eval (p : Circle F).x + (p : Circle F).y * b.eval (p : Circle F).x }
```

(using `y² = 1 − x²` to reduce every element of `F[x,y]/(x²+y²−1)` to the form `a(x) + y·b(x)`),
plus one line for the `x`-projection `D.image (·.x)`.  This was elaborated in a scratch file to
confirm it type-checks; **it has deliberately not been added to the repository**, because a
definition with no theorem attached is decoration and would create the appearance of a bridge
that does not exist.

**Content: no.**  Two steps carry everything, and neither is a fifteen-line job:

1. **Minimum distance of the circle code on a twin coset.**  This is the step that unlocks
   everything else, because the MCA layer of this repository is *already* alphabet- and
   code-generic: `Root.CodingTheory.Alphabet.card_badSet_le` and `Alphabet.epsMCAmax_le`
   (`RequestProject/Root/CodingTheory/AlphabetMCA.lean`) hold for an arbitrary submodule
   `C ⊆ (ι → A)` under `MinDistGe C d` and `3e < d`.  A circle code with a proved distance
   bound would therefore inherit `ε_mca ≤ n/|F|` with no new MCA theory at all — this is the
   cheapest available route to a first circle statement, and it is recorded here as the
   recommended entry point for any future attempt.
2. **Identification of the circle fold's second layer with the odd part of the `x`-projection.**
   This is what would let `RESULTS.md` §75 transfer verbatim and replace `n/|F|` by the sharp
   `1/|F|` in the degree window.

Until (1) exists, no circle statement of any kind is available; until (2) exists, the sharp
one is not.  The gap is left open and is stated as such: **no Circle-STARK certificate is
claimed in this repository.**
