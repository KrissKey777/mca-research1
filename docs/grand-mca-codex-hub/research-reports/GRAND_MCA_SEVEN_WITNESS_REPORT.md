# Grand MCA — the compressed seven-witness certificate at `RS[F_17^32, μ_512, 256]`

**Verdict: `[GRAND-MCA-UNSAFE-7]`.**  For the requested row there is now a machine-checked,
`sorry`-free certificate: one fixed pair `(f₀, f₁)` and seven pairwise distinct challenges
that are officially bad, hence

  `ε_mca(RS_256(μ_512) over F_{17^32}, δ = 125/256) ≥ 7/17^32 > 2^{-128}`.

The certificate is **independent of the Cycle84 census**: it does not use, and does not need,
the `52,747,567,092` count, the seven-slot colour shell, or the Cycle116/119 fixed-jet
transfer.  Consequently no transfer audit is required for the conclusion, and the mission's
"do not replay the census" instruction is satisfied in the strongest possible way — the census
is not on the dependency path at all.  (The Cycle84/116/119/120 packet is not present in this
repository; nothing here was checked against it.)

File: `RequestProject/Root/CodingTheory/GrandMCASevenWitness.lean` (builds clean, no `sorry`,
axioms `propext`, `Classical.choice`, `Quot.sound` only).

---

## 1. The row, exactly

| item | value |
|---|---|
| code field | `K = F_{17^32}`, `|K| = 17^32 = 2367911594760467245844106297320951247361` |
| domain | `H = μ_512 = ⟨θ⟩ ⊆ K^*`, `n = 512 = 2^9` |
| smoothness | `v₂(17^32 − 1) = 9`, so `512 ∣ 17^32 − 1` and `H` is the full 2-Sylow of `K^*` |
| code | `C = RS_256(H)`, rate `1/2` |
| radius | `e = 250`, `δ = 250/512 = 125/256` |
| closed agreement threshold | `n − e = 262` |
| needed witnesses | `⌊17^32 / 2^128⌋ = 6`, hence **7** |

`7·2^128 = 2381976568446569244243622252022377480192 > 17^32`; seven challenges give density
`2^{-127.9915}`, just over the `2^{-128}` line, exactly as the mission's compression states.

## 2. The certificate

Fixed pencil on `H` (one pair for all seven challenges):

  `f₀(x) = x^264`,  `f₁(x) = x^256`.

Block structure: `H` is the disjoint union of the `64` cosets of `μ_8`; the `i`-th coset has
vanishing polynomial `X^8 − b_i` with `b_i = θ^{8i}` (`i < 64`), and the `b_i` are exactly the
`64`-th roots of unity.

Witness supports: for `t < 32` let `I_t = {0,1,…,31} ∪ {32+t} ⊆ {0,…,63}` (33 blocks) and

  `S_t = ⋃_{i ∈ I_t} (i-th coset)`,  `|S_t| = 33·8 = 264`.

Its vanishing polynomial is `∏_{i∈I_t}(X^8 − b_i) = X^264 − (Σ_{i∈I_t} b_i)·X^256 + R` with
`deg R ≤ 248 < 256`, because every exponent occurring in the product is a multiple of `8`.
Hence, on `S_t`,

  `f₀ + γ_t·f₁ = −R`,  `deg R < 256`,  with  `γ_t = −Σ_{i ∈ I_t} b_i = −(Σ_{i<32} θ^{8i} + θ^{256+8t})`,

so `f₀ + γ_t f₁` **is** explained by `C` on `S_t`, while `f₁ = x^256` restricted to `S_t`
interpolates to `X^256` itself (degree `256 ≥ 256`, and `256 < |S_t| = 264`), so `(f₀, f₁)` is
**not** simultaneously explained on that same `S_t`.  This is precisely the official
same-support event.

Distinctness is immediate — the seven challenges differ only in the single swapped block
parameter `θ^{256+8t}`, and `θ` has order `512 > 256 + 8·31`.

Agreement is `264`, not merely `262`: the witnesses satisfy the requested Cycle119
strengthening (`≥ 263`, distance `248 ≤ 249 < 250`) at no extra cost, so both the closed and
the strict reading of the ball are covered (`isBad_wit` at radius `248`, `isBad_wit_249`,
and `isBad_of_radius_le` up to the official `250`).

## 3. What is in Lean

| declaration | statement |
|---|---|
| `mulDomain`, `mulCoset`, `prod_mulCoset`, `card_mulCoset`, `disjoint_mulCoset`, `card_mulDomain` | `μ_d`-coset decomposition of `μ_{dm}` **over an arbitrary field** (the repository previously had only the `ZMod p`, powers-of-two version in `CapacityGapCosets`) |
| `isBad_of_radius_le`, `badSet_subset_of_radius_le` | radius monotonicity of the official predicate |
| `card_image_le_card_badSet_blocks` | any family of `(s+1)`-block sets injects its challenges into the bad set (the counting step of `card_badSet_ge_blocks_halfGap` without a global dissociativity hypothesis) |
| `GrandMCASeven.card_K` | `|F_{17^32}| = 17^32` |
| `GrandMCASeven.exists_primitiveRoot_512` | `K` contains a primitive `512`-th root of unity |
| `GrandMCASeven.isBad_wit` | each of the `32` (in particular the seven) challenges is officially bad at radius `248` |
| `GrandMCASeven.official_event` | the event unfolded: a support of `264` positions carrying `f₀ + γ_t f₁` but not the pair |
| `GrandMCASeven.card_gammas` | the seven challenges are pairwise distinct |
| `GrandMCASeven.seven_le_card_badSet` | `7 ≤ #Bad` at the official radius `250` |
| `GrandMCASeven.two_pow_neg_128_lt` | `2^{-128} < 7/17^32` |
| `GrandMCASeven.epsMCA_gt_two_pow_neg_128` | `ε_mca > 2^{-128}` for the fixed pencil |
| `GrandMCASeven.exists_grandMCA_seven_witness` | the unconditional packaged form |

The mechanism is the project's own block pencil (`HalfGapPencil.isBad_blocks_halfGap`) at
block size `d = 8`, `s + 1 = 33` blocks, `j = 0`, i.e. absolute gap `c = 8` for the witnesses;
the official row's gap `c = 6` is reached by radius monotonicity (`248 ≤ 250`).  Since
`C(64,33) = 1777090076065542336`, the same pencil in fact carries astronomically more bad
challenges than seven, but proving a count that large would need a dissociativity statement
for sums of `33` of the `64`-th roots of unity; the mission needs only seven, and seven come
with a two-line distinctness argument.

An independent numerical replay of the identical construction (scaled to `n = 32`, `d = 8`,
`k = 16`, window `24` over `F_97`, `analysis/`) confirms the predicted challenges are bad and
that `f₁` is not explained on the same window.

## 4. Source/authority gate — what was and was not checked

The predicate certified is the project's official `Root.CodingTheory.IsBad` and its measure
`epsMCA`: `γ` is bad iff **some** support `S` with `|D| ≤ |S| + e` (closed threshold) carries
`f₀ + γ f₁` as a codeword restriction while the pair `(f₀,f₁)` is not simultaneously explained
on that same `S`; `epsMCA` is the uniform measure over the **whole** code field `K`, with no
separate challenge alphabet.  The row uses an arbitrary finite field, a smooth multiplicative
subgroup as domain, and rate `1/2`.

No external document was consulted while producing this file — there is no network access in
this environment and the Cycle120 extraction is not in the repository.  Therefore this report
does **not** certify agreement with any printed Definition 4.3; it certifies the event as
formalised above.  If an authoritative definition differs on any of the four points (field,
domain, challenge alphabet, closed vs strict threshold), the affected item is:

* strict vs closed threshold — **already covered**: agreement `264 ≥ 263`;
* challenge alphabet — the seven `γ_t` lie in `K` and are distinct; if a definition restricted
  challenges to a subfield or to a `q_chal`-sized set, the certificate would have to be
  re-run with the block parameters chosen inside that set (not attempted here);
* field/domain/rate — the construction is generic in `d, m, s`, so it transfers verbatim.

## 5. Secondary: the `c = 2` Plücker route (paused, with data)

Work done before the priority reset, kept because it independently confirms the warning in the
mission that support counts exaggerate badness.

* **Exact `c = 2` dictionary** (`analysis/gr2_c2_kernel.py`, validated against direct
  interpolation on all supports, zero mismatches): with `Z_D'(x) = ∏_{z≠x}(x−z)`,
  `L_j(f) = Σ_{x∈D} x^j f(x) Λ_E(x)/Z_D'(x)`, one has `W ∩ U_E ≠ 0` iff
  `Ω(E) = L_0(f₀)L_1(f₁) − L_0(f₁)L_1(f₀) = 0`, and

    `Ω(E) = Σ_{x,y∈D} (y−x)·g₀(x)Λ_E(x)·g₁(y)Λ_E(y)`,  `g_i = f_i/Z_D'`,

  an **alternating bilinear form** in `(f₀,f₁)`.  So at `c = 2` the incidence condition is a
  single *linear* condition on the Plücker coordinates of the plane: `⟨ω_E, f₀ ∧ f₁⟩ = 0` with
  kernel `ω_E(x,y) = (y−x)Λ_E(x)Λ_E(y)/(Z_D'(x)Z_D'(y))`.
* **Support counts are not challenge counts** (`analysis/gr2_c2_experiments.py`, `|F| = 10^6`):
  a plane containing the syndrome of a *weight-1* error has exactly `C(n−1, e−1)` incident
  supports — `165` for `RS[12,6], e=4` and `3003` for `RS[16,8], e=6` — all of which collapse
  to a **single** challenge, against the graded optimum of `15` resp. `56` challenges.  Random
  planes at `|F| = 10^6` have `0` incidences.  So "unusually many incident supports" carries no
  structural information whatsoever, and the dichotomy must be stated for *challenges*; this
  agrees with the mission's own `285/495 → ≈2 challenges` observation.
* **Exact classification at `e = 2`** (`analysis/gr2_c2_klein.py`): there `κ = 4`, the `U_E` are
  the secant lines of a rational normal curve in `P^3`, and incidence is orthogonality on the
  Klein quadric.  Enumerating all 4-subsets of the `C(n,2)` Plücker hyperplanes finds *every*
  plane with `≥ 4` incidences exactly.  At `q = 1009`: for `n = 8`, `k = 4` the maximum
  incidence count is `13 = 1 + 2(n−2)`, and every extremizer inspected is a degenerate plane
  `W = U_{E₀}` (one containment branch, only `2` challenges — the two curve points of `E₀`);
  the same happens at `n = 6` (`9 = 1 + 2·4`).  The maximum *challenge* count, by contrast, is
  `4 = C(4,3)` — the graded optimum — attained on the `μ_2`-graded domain and not beaten on a
  generic domain (max `3` there).  No non-block extremizer was found.

This route is paused, not closed: it should be resumed on the coloured map `E ↦ γ(E)` rather
than on raw incidences.
