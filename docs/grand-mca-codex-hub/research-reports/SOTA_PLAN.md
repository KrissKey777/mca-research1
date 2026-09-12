# SOTA_PLAN — where the MCA / proximity-gap development stands, and what is left

This file is the standing status board for the two tracks of the current mission.  It is
deliberately short and factual: every entry is either **proved** (a Lean declaration that
compiles with no `sorry` and whose `#print axioms` output is exactly
`propext, Classical.choice, Quot.sound`), **refuted** (an explicit kernel-checked
counterexample), or **open** (no proof, no counterexample — stated as such, never hidden).

Cross-references: `RESULTS.md` (statements and proofs), `DISCREPANCIES.md` (every place where
the literature, an informal brief, or an earlier plan disagrees with what is actually proved),
`CIRCLE_STARK_INTERFACE_AUDIT.md` (what would be needed for a Circle-STARK application).

---

## 1. Strict unique-decoding window — CLOSED (refuted)

**Question.** Does `k + 2e < |D|` force `#Bad ≤ e + 1` for the project's *strong* bad set?

**Answer: no.**  `Root.CodingTheory.not_forall_card_badSet_le_succ_radius_strict_window`
(`RequestProject/Root/CodingTheory/StrictWindowRefutation.lean`).  Witness: `ZMod 11`,
`|D| = 8`, `k = 3`, `e = 2`, so `k + 2e = 7 < 8 = |D|`, and `#Bad ≥ 4 > 3 = e + 1`.  The
Welch–Berlekamp pencil of the witness is degenerate (`StrictWindowWitness.wbDet_eq_zero`), so
the nondegenerate route `card_badSet_le_of_wbDet_ne_zero` genuinely does not apply and the
refutation is not an artefact of a missing case.

**Consequence for the hypothesis budget.**  The proved anchor
`card_badSet_le_succ_radius` needs `k + 3e ≤ |D|`, and that `3e` cannot be relaxed to `2e`:
`not_forall_card_badSet_le_succ_radius_of_two_radius` refutes even the weak boundary
`2e = |D| − k`, there with `#Bad = |D|` (the trivial bound).  Both boundaries are therefore
settled; **do not reopen them.**

## 2. Syndrome/MDS certificate at rate ρ = 1/2 — CLOSED (proved)

`RequestProject/Root/CodingTheory/RhoHalfSyndromeCertificate.lean`, all declarations
kernel-checked.

| route | `n = |D|` | `k` (ρ) | `e` (δ) | field size needed for `ε_mca ≤ 2⁻¹²⁸` |
|---|---:|---|---|---|
| circuit / MDS | `2²⁰` | `2¹⁹` (1/2) | `314572` (δ ≈ 0.2999992) | `|F| ≥ 2^699180` |
| counting (`#Bad ≤ e+1`) | `2²⁰` | `2¹⁹` (1/2) | `⌊n/6⌋` (δ = 1/6) | `|F| ≥ 2¹⁴⁶` |
| counting (`#Bad ≤ e+1`) | `2²⁰` | `2¹⁸` (1/4) | `⌊n/4⌋` (δ = 1/4) | `|F| ≥ 2¹⁴⁷` |
| GS/Johnson (pre-existing) | `2²⁰` | `2¹⁹` (1/2) | `109801` (δ ≈ 0.1047) | `|F| ≥ 2¹⁵¹` |

**Two-sided bracket for the circuit route.**  `[2²⁰⁹⁷¹⁴, 2⁶⁹⁹⁰⁵²]`; the exact ratio has bit
length 415043 (exact integer arithmetic).  So the bracket is genuine but not tight, and the
*method* provably cannot certify `2⁻¹²⁸` at those parameters with a field below `2²⁰⁹⁸⁴²`
(`lower_core`, `choose_ratio_ge_rho_half`).

**Reading it honestly.**  δ ≈ 0.3 exceeds both the unique-decoding radius `1/4` and the
Johnson radius `1 − √(1/2) ≈ 0.2929`, but only at exponential field size, so **no
post-Johnson and no capacity claim is made or implied.**  The practically usable rate-1/2
statement is the counting one (δ = 1/6, `|F| ≥ 2¹⁴⁶`), which at ρ = 1/2 strictly dominates
the GS/Johnson route (δ = 1/6 > 0.1464… = the half-Johnson threshold `(1−√ρ)/2`) both in
radius and in required field size.

**Structural gap that remains open.**  For δ strictly between `1/6` and `≈0.29` at ρ = 1/2
there is *no* certificate with sub-exponential field size, and none is claimed.  Closing that
gap needs the trivariate/Hensel extraction of BCIKS20 §5 (see the scope note in
`MCAJohnsonGS.lean`), not a better counting argument: the obstruction is that correlated
agreement is extracted from two points of a line at radius `2e`.

## 3. Monomial packets on multi-coset domains — CLOSED (refuted beyond two cosets)

`RequestProject/Root/CodingTheory/MulticosetMonomialWitness.lean`.

* One coset, and two cosets `H ∪ cH`: `#Bad ≤ 1` survived every scanned instance
  (2.1 M instances, exact arithmetic, `q ∈ {5,…,31}`) — **open**, no proof attempted.
* Three cosets: **refuted.**  `not_forall_monomial_card_badSet_le_one` — over `ZMod 13`
  with `D = {±1, ±2, ±3}`, `k = 2`, `e = 1`, packet `f₀ = t⁴`, `f₁ = t⁵`, the bad set is
  `{1, 12}`.
* The weaker `#Bad ≤ s` (`s` = number of cosets) is now **refuted** as well
  (`not_forall_monomial_card_badSet_le_three_cosets`, `RESULTS.md` §77): the completed slice
  scan on `e + 1 > s` gives 18 violations on three cosets, and the smallest one is formalized
  — `ZMod 17`, `D = H ∪ 2H ∪ 3H` of size 12, `k = 2`, `e = 3`, `f₀ = t⁸`, `f₁ = t⁹`,
  bad set `{6,7,10,11}`, so `#Bad = 4 > 3 = s`.
* Sensitivity control: on the same domains, general non-monomial packets do reach
  `#Bad = 2`, so the monomial ceiling is a property of the packets, not of the scanner.

Note also (`DISCREPANCIES.md`, D73.1): the "monomial theorem" and "multilayer" files cited by
the incoming brief **do not exist in this repository**, and no result of that name was ever
proved here; the claim was therefore re-tested from scratch rather than assumed.

## 4. Structured second layer and the degree trichotomy — PARTIALLY PROVED

`RequestProject/Root/CodingTheory/StructuredSecondLayer.lean` (`RESULTS.md` §74).  For a line
whose **second layer** is the evaluation of a single polynomial `g` — with *no* hypothesis on
the first layer:

| regime | condition | bound | status |
|---|---|---|---|
| codeword | `deg g < k` | `#Bad = 0` | **proved** (`badSet_eq_empty_of_codeword_snd`) |
| structural | `k ≤ deg g < t`, `2e + t ≤ |D|` | `#Bad ≤ 1` | **proved** (`card_badSet_le_one_of_structured_snd`) |
| degenerate | `deg g ≥ t` | not bounded by 1 | **refuted** (the §73 witness has `deg g = 5 ≥ t`) |
| sharpness of the two boundaries | `deg g = k−1` vs `k`, `t−1` vs `t` | — | **open** (no witness formalized) |

New certificate row for the rate-1/2 table of §2 above:

| route | `n = |D|` | `k` (ρ) | `e` (δ) | field size for `ε_mca ≤ 2⁻¹²⁸` |
|---|---:|---|---|---|
| structured second layer (`deg g = k`) | `2²⁰` | `2¹⁹` (1/2) | `262143` (δ ≈ 0.2499990) | `|F| ≥ 2¹²⁸` |

**Scope, stated once and not to be dropped when quoting:** this bounds `ε_mca` of a *line
satisfying the structural hypothesis*, not `epsMCAmax` over all lines.  `δ < 1/4` is inside
unique decoding; nothing post-Johnson, nothing about capacity.

## 5. Radix-2 (FRI) fold — CONNECTED

`RequestProject/Root/CodingTheory/FRIFoldStructured.lean` (`RESULTS.md` §75).  The second
layer of one FRI round applied to a word that is the evaluation of a single polynomial `P` is
*itself* the evaluation of a single polynomial, `oddPart P`, of degree `⌊(deg P − 1)/2⌋`
(`friSnd_eval`, `degree_oddPart_eq_of_natDegree`).  So §4 applies with no extra assumption on
the layer, and the trichotomy becomes a statement about `deg P`:

* `deg P < 2k` ⇒ `#Bad = 0` (`fri_fold_badSet_eq_empty_of_low_degree`);
* `deg P = 2m+1`, `k ≤ m < t`, `2e + t ≤ |D|` ⇒ `#Bad ≤ 1`, `ε_mca ≤ 1/|F|`
  (`fri_fold_card_badSet_le_one`, `fri_fold_epsMCA_le`);
* concrete round: `|D| = 2²⁰`, `k = 2¹⁹`, `e = 262143`, `deg P = 2²⁰+1` ⇒ `ε_mca ≤ 2⁻¹²⁸`
  for `|F| ≥ 2¹²⁸` (`fri_round_epsMCA_le_two_pow_neg_128`).

**Open:** the fully adversarial prover (word not a polynomial evaluation), where only
`#Bad ≤ e + 1` is available.

## 6. Circle-STARK interface — AUDITED, not connected

`CIRCLE_STARK_INTERFACE_AUDIT.md`.  The circle development (`RequestProject/Circle*.lean`)
and the coding-theory development (`RequestProject/Root/CodingTheory/`) are literally
disjoint — no file of one refers to the other.  The two missing pieces, in order:

1. a definition of the circle code as a submodule of functions on a twin-coset domain;
2. a bridge from that code to univariate RS through the 2-to-1 `x`-projection, so that the
   existing `epsMCAmax_…` bounds transfer.

**Feasibility probe (session closure).**  The *definition* (1) is about a dozen lines and was
confirmed to elaborate in a scratch file, but was not committed: it proves nothing on its own.
The content is in the minimum-distance bound for that submodule, after which the
alphabet-generic layer `Root.CodingTheory.Alphabet.card_badSet_le` / `epsMCAmax_le` applies to
it verbatim (any submodule code with `MinDistGe C d`, `3e < d`, giving `ε_mca ≤ n/|F|`); the
sharp `1/|F|` additionally needs (2).  Recorded in `CIRCLE_STARK_INTERFACE_AUDIT.md` §7 and
`RESULTS.md` §78.2 as future work.

Until (1) and (2) exist, **no Circle-STARK certificate is claimed.**  Re-audited after §74–§75
(`RESULTS.md` §76): the failing condition is not one of the degree inequalities of §4 — it is
that the circle code, hence the circle bad set, is not defined in this repository at all.  The
univariate FRI round of §5 is the certificate that does exist.

---

## Closed routes — do not reopen

* the weak boundary `2e = |D| − k` and the strict window `k + 2e < |D|` (both refuted above);
* repeated-factor elimination; squarefree residual kernels;
* bounding the codeword locus by the list size;
* naive `L ≥ 3` scaling of the line-decodability argument;
* the monomial sharpening `#Bad ≤ 1` beyond two cosets, and the coset-count bound `#Bad ≤ s`
  (both refuted, §73 and §77);
* gcd/resultant routes to `Q` squarefreeness;
* capacity for ordinary RS (only the folded-RS capacity results stand).

## Method rules that produced these results

* Refutation first: every candidate statement is scanned exhaustively in exact
  integer/`Fraction` arithmetic (no floats) *before* any Lean is written, with at least two
  independent engines wherever a claim is load-bearing, plus a sensitivity control that must
  reproduce known positive counts.
* Only the weakest surviving statement is formalized; counterexamples are formalized as
  first-class negative results, not left in a script.
* Very large numerals (e.g. `2^524288`) force a specific Lean style: all algebra in lemmas
  with *variable* exponents, one concrete instantiation per top-level theorem.  Monolithic
  proof terms hit `maximum recursion depth` / kernel deep recursion.

---

## Phase status at session closure

Consolidated, frozen, and documented (`RESULTS.md` §78):

* **proved** — the structured second layer (§4), the FRI fold bridge (§5), and the one-round
  certificate `ε_mca ≤ 2⁻¹²⁸` at `ρ = 1/2`, `δ ≈ 0.25`, which is unconditional *given the fold
  hypothesis* (the prover's word is the evaluation of a single polynomial of the stated
  degree) — one round, one line;
* **refuted** — the coset-count bound `#Bad ≤ s` (§3);
* **open** — the Circle-STARK interface (§6), the only missing bridge, left as future work.

Full `lake build` is clean (8199 jobs), no `sorry`/`admit` anywhere in `RequestProject/`, and
no axioms beyond `propext, Classical.choice, Quot.sound`.

## 7. Circle code — one bridge proved (run of 2026-08-27)

**Route chosen: zero count (C).**  The structured-second-layer theorem was re-proved in the
form its proof actually supports — an arbitrary linear code over an arbitrary alphabet, with a
certified zero count for the second layer (`Alphabet.card_badSet_le_one_of_zeroCount`,
`ZeroCountSecondLayer.lean`) — and then instantiated at the circle code
(`CircleZeroCount.lean`).

| item | status |
|---|---|
| circle word = ordinary polynomial evaluation | **refuted** (explicit counterexample) |
| circle code as rank-two module / quotient ring | confirmed; this is the right structure |
| zero count `#zeros ≤ deg(a² − (1−x²)b²) ≤ 2t` | **proved** (char ≠ 2 required and necessary) |
| `#Bad ≤ 1` for a structured circle second layer, `2e + 2t + 1 ≤ |D|` | **proved** |
| `ε_mca ≤ 1/|F|`, and `≤ 2⁻¹²⁸` at `ρ = 1/2`, `δ ≈ 0.2499981` | **proved** |
| slack `+1` removable | **no** — witness with `#Bad = 2` at `2e + 2t = |D|` |
| minimum distance suffices instead of the window | **no** — witness with `#Bad = 2` at `3e < d` |
| one circle round ↔ folded univariate instance | **different quantities** — separating examples |
| Circle-STARK soundness | still not claimed; unchanged open gap |

**Next highest-value target.**  The remaining gap between this per-line circle certificate and
a protocol statement is the *prover-word* side: for the univariate fold, `friSnd_eval` derives
the structural hypothesis from "the prover's word is one polynomial".  The circle analogue
would be a lemma deriving `f₁ = circleWord D a b` with `deg a, deg b < t` from a statement about
the prover's circle word in one Circle-FRI round — a statement about the protocol, not about
the code, and the honest next step before any Circle-STARK claim.
