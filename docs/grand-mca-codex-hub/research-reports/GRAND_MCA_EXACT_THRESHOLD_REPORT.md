# Grand MCA — an **exact** row: `RS[F_q, μ_512, 256]`, `q = 5·2^127 + 1`

**Verdict: `[GRAND-MCA-EXACT-ROW]` together with `[DEFINITION-ENDPOINT]`.**

Both sides of one Grand-MCA row are now machine-checked, `sorry`-free, with only the default
Lean/Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).  The critical integer radius
of the row is pinned exactly, and the "largest `δ*`" phrasing is shown not to have a literal
solution at finite block length.

Files:

* `RequestProject/Root/CodingTheory/ProthPrimeCertificate.lean` — primality of the field size;
* `RequestProject/Root/CodingTheory/GrandMCAExactThreshold.lean` — the general triangle
  mechanism and the exact row.

---

## 1. The row

| item | value |
|---|---|
| code field | `F = F_q`, `q = 5·2^127 + 1 = 850705917302346158658436518579420528641` (**prime**, certified) |
| domain | `H = μ_512 = ⟨θ⟩ ⊆ F^*`, `n = 512 = 2^9` (smooth) |
| smoothness slack | `q − 1 = 5·2^127`, so `512 ∣ q − 1` with `2^118` to spare |
| code | `C = RS_256(H)`, rate `1/2` |
| threshold | `ε* = 2^{-128}` |
| key arithmetic | `2^129 < q < 3·2^128`, hence `⌊q/2^128⌋ = 2` |

Because the challenge is uniform over the whole field, at this field size

* `#Bad ≤ 2  ⟹  ε_mca ≤ 2/q < 2^{-128}` (safe);
* `#Bad ≥ 3  ⟹  ε_mca ≥ 3/q > 2^{-128}` (unsafe).

So the security question collapses to: *does some line have three bad challenges?*

## 2. Primality: a Lucas certificate, and a correction to the submitted one

The submitted packet proposed the Proth witness `3` (`3^{(q−1)/2} ≡ −1 mod q`).  That
congruence is true, but it is **not** usable with Mathlib's `lucas_primality`, which needs a
base of full order `q − 1`, i.e. one that is a non-residue for *both* prime divisors `2` and
`5` of `q − 1 = 5·2^127`.  An exact computation shows

  `3^{(q−1)/5} ≡ 1 (mod q)`,

so `3` has order `2^127`, not `q − 1`, and the Lucas route fails with base `3`.  The base
`17` works: `17^{(q−1)/2} ≡ −1` and `17^{(q−1)/5} ≢ 1`.  This is what
`Root.NumberTheory.qProth_prime` certifies, via an explicit chain of `127` repeated squarings
(each step a `norm_num` computation on 130-bit numerals) plus two fifth powers.  No
`native_decide`, no axioms beyond the defaults.

(The Proth theorem itself would of course also prove primality; it is not in Mathlib, and the
Lucas route with base `17` is cheaper than formalising it.)

## 3. Unsafe side — the triangle line (general theorem)

For three distinct domain points `a, b, c` put

  `f₀ = 2·1_a + 1_b`,  `f₁ = −1_a − 1_b + 1_c`.

The line point at `γ` takes the value `2 − γ` at `a`, `1 − γ` at `b`, `γ` at `c`, and `0`
elsewhere.  Hence

| `γ` | line point support | witness support `S_γ` | `|S_γ|` |
|---|---|---|---|
| `0` | `{a,b}` | `H ∖ {a,b}` | `n − 2` |
| `1` | `{a,c}` | `H ∖ {a,c}` | `n − 2` |
| `2` | `{b,c}` | `H ∖ {b,c}` | `n − 2` |

On each `S_γ` the `γ`-point of the line is *identically zero*, hence explained by the zero
codeword; and on the same `S_γ` some other point of the line is a **one-hot** word (value `2`
at `c` for `γ' = 2` on `S_0`; value `1` at `b` and value `2` at `a` for `γ' = 0` on `S_1`,
`S_2`).  A polynomial of degree `< k` agreeing with a one-hot word on `S` would have
`|S| − 1 ≥ k` roots, so it is zero — contradicting the nonzero coordinate.  Therefore the
whole line is not explained on `S_γ`, and `γ` is officially bad.

Formal statements (`Root.CodingTheory`, general field, `char F ≠ 2`, `k + 3 ≤ |D|`):
`not_isCloseOn_oneHot`, `isBad_of_oneHot_witness`, `triangle_isBad_zero/one/two`,
`three_le_card_badSet_triangle`, and `card_badSet_triangle_eq_three` (with `1 ≤ k`,
`k + 6 ≤ |D|`).

For the row: `k = 256`, `e = 2`, `n = 512`, `δ = 2/512 = 1/256`, three bad challenges
`0, 1, 2`, so `ε_mca ≥ 3/q > 2^{-128}` — `ExactRow.epsMCA_two_gt`, and at every larger radius
`ExactRow.epsMCA_gt_of_two_le`.

## 4. Safe side — from the project's own dichotomy

`BadSetPencilBound.card_badSet_le_succ_radius_of_le` (already in the repository,
`sorry`-free) gives `#Bad ≤ e + 1` whenever `1 ≤ k`, `k ≤ |D|` and `k + 3e ≤ |D|`.  At this
row `k + 3e = 256 + 3e ≤ 512` for every `e ≤ 1`, so **every** line has `#Bad ≤ 2` and

  `ε_mca ≤ 2/q < 2^{-128}`  (`ExactRow.epsMCA_le_of_radius_le_one`),

and the same bound for the code, i.e. the maximum over lines
(`ExactRow.epsMCAmax_le_of_radius_le_one`).

The connection asserted in the submitted packet is therefore confirmed against the exact
theorem statement — with one clarification: the useful form is
`card_badSet_le_succ_radius_of_le` (`k + 3e ≤ |D| → #Bad ≤ e + 1`), not the raw dichotomy
`card_badSet_le_or_card_lt`, and the hypothesis check is `256 + 3·1 = 259 ≤ 512`, not
`512 ≥ 256 + 3` read at `e = 1` only by accident.

## 5. The exact transition, and the endpoint

* `e = 1`: safe (every line).  `e = 2`: unsafe (explicit line).  Hence `e_crit = 2`, and at
  `e = 2` the triangle line has **exactly** three bad challenges
  (`ExactRow.card_badSet_eq_three`) — so the `e + 1` cap of the project's dichotomy is sharp
  at `e = 2`.
* Reading a real radius `δ` as the integer radius `⌊δ·n⌋`, the set of safe radii is exactly
  `[0, 1/256)` (`ExactRow.safeRadii_eq`), whose supremum is `δ* = 1/256`
  (`ExactRow.isLUB_safeRadii`) and which does **not** contain `1/256`
  (`ExactRow.one_div_256_notMem_safeRadii`).

So at finite block length with the closed threshold `|S| ≥ (1−δ)n`, `ε_mca(C,·)` is a step
function and the literal "largest `δ*` with `ε_mca(C,δ*) ≤ ε*`" does not exist for this row.
The two well-posed formulations are the critical integer radius (`e_crit = 2`) and the
supremal safe radius (`δ* = 1/256`, not attained).  Both are proved.

## 6. Comparison with the earlier rows of this project

| construction | field | `δ` reached | witnesses |
|---|---|---|---|
| Cycle116 coset pencil (`GrandMCASevenWitness.lean`) | `F_{17^32}` | `125/256` | 7 |
| `μ_8`-coset variant (block size `64`) | `F_{17^32}` | `3/8` | 16 (not formalised) |
| `μ_4`-coset variant (block size `128`) | `F_{17^32}` | `1/4` | ≤ 4 — too few for `2^{-128}` |
| **triangle line, this file** | `F_q`, `q = 5·2^127+1` | **`1/256`** | 3 (exactly `e+1`) |

The collapse is not a better mechanism for a *fixed* field: it is the combination of a much
smaller field (where `3` witnesses already break `2^{-128}`) with a construction that needs
only `e = 2` errors.  The coset mechanisms need `Ω(n)` errors because their witness supports
are unions of whole cosets; the triangle needs two.  Consequently the earlier `3/8` and `1/4`
questions are moot for the security threshold at this row and the `m = 8` optimality
discussion of the coset mechanism is superseded here (that discussion remains correct *within*
the coset mechanism over `F_{17^32}`).

Note the general triangle theorem is *not* a specialisation of `HalfGapPencil`: the half-gap
pencil produces power words `x^{ds+d}, x^{ds}` with coset-union witness supports and its bad
challenges are block sums, whereas the triangle uses weight-`≤ 3` indicator words and
`|D| − 2`-sized supports.  The two mechanisms are incomparable in shape; the triangle is
strictly stronger in the only respect that matters for a security threshold — it reaches
`#Bad ≥ 3` at `e = 2`, the smallest radius at which `#Bad ≥ 3` is possible at all (the
dichotomy forbids it for `e ≤ 1`).

## 7. Prior-work audit (honest scope)

There is **no network access in this environment**, and no copy of Arnon–Boneh–Fenzi
(ePrint 2026/680), BCHKS/BCIKS, Haböck, BCGM, Crites–Stewart, or Krachun–Kazanin/CGHLL is
present in this repository.  Therefore this report does **not** certify agreement with any
printed definition, and it does not claim novelty against those texts.  What is certified is
the event as formalised by the project's own `Root.CodingTheory.IsBad` / `epsMCA`:

* `γ` is bad iff **some** support `S` with `|D| ≤ |S| + e` (closed threshold) carries
  `f₀ + γ f₁` as a codeword restriction while the *pair* `(f₀,f₁)` is not simultaneously
  explained on that same `S`;
* `epsMCA` is the uniform measure over the whole field `F`;
* `epsMCAmax` is the maximum over all pairs `(f₀,f₁)`.

These are exactly the four features listed in the mission's transcription of Definition 4.3
(uniform `γ` over `F`, closed threshold, `γ`-dependent support, same-support noncontainment).
Should the authoritative text differ on any of them, the affected item would have to be
re-checked; the constructions are robust to the strict/closed distinction (agreement `510`
versus the closed threshold `510`, and the safe side is proved for all `e ≤ 1`).

On novelty: weight-`O(1)` indicator counterexamples to correlated agreement at radii just
above the "`e + 1`" regime are folklore-adjacent — the project itself already contains
indicator-word witnesses (`UniqueDecodingGapWitness.lean`, `UniqueDecodingHoleWitness.lean`).
What is new here is (i) the parameter-free general form with the exact count `#Bad = e + 1 = 3`,
and (ii) the field-size engineering that makes the two sides *meet*, giving an exact threshold
rather than another lower bound.

## 8. What this does **not** say

* It does not say that RS codes are insecure in the regime practitioners use: the row is
  unsafe only because `q ≈ 2^129.7` is deliberately tiny relative to `2^{-128}`, so three bad
  challenges already exceed the threshold.  Over a `256`-bit field the same triangle gives
  `3/q ≈ 2^{-254}`, far below the threshold.
* It does not pin the threshold for any other field or rate; the safe side used here is the
  generic `#Bad ≤ e + 1` bound, which stops being useful as soon as `k + 3e > n`.
