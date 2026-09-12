# SUBRESULTANT STRENGTH GATE

Subject theorem (machine-checked, axiom-clean, no `sorry`):

`Root.CodingTheory.Subresultant.card_badSet_le_unconditional`
(`RequestProject/Root/CodingTheory/SubresultantCorrelatedBridge.lean:803`)

```
theorem card_badSet_le_unconditional (hk : 1 ≤ k) (hkD : k + 2 * e ≤ D.card) :
    (badSet k e f₀ f₁).card ≤ (k + 1) * e + 1
```
Ambient: `{F} [Field F] [DecidableEq F] [Fintype F] {D : Finset F} {k e : ℕ} {f₀ f₁ : ↥D → F}`.
No structural hypothesis (no nonzero Welch–Berlekamp kernel, no condition on `W_can`).
All integer values below are exact integer arithmetic done outside Lean (the freeze forbids
Lean edits/builds); they are stated as arithmetic facts, not as machine-checked Lean lemmas.

## 1. MCA conversion status

There is **no dedicated `ε_mca` corollary of the subresultant theorem** in the project:
`SubresultantCorrelatedBridge.lean` never mentions `epsMCA`. The conversion is nevertheless
exact and definitional, via two existing declarations:

* `Root.CodingTheory.epsMCA` (`MCA.lean:128`):
  `epsMCA k e f₀ f₁ := Root.FinProb.probOf (Root.FinProb.uniform F) (badSet k e f₀ f₁)` —
  the uniform challenge on the whole field `F`, and *the same* `badSet k e f₀ f₁`
  (`MCA.lean:115`) as in the subresultant theorem.
* `Root.FinProb.probOf_uniform` (`Root/Prob.lean:349`), hypotheses `[Fintype α] [Nonempty α]`:
  `probOf (uniform α) s = s.card / Fintype.card α`.

Hence `ε_mca = #Bad / |F|` **exactly** (not merely `≤`), so
`ε_mca ≤ ((k+1)e + 1)/|F|` follows from the subresultant theorem by one rewriting step —
but that corollary is not yet a declaration in the project. Status: **conversion verified at
the definition level, corollary not instantiated.**

## 2. Exact strength table (`n = |D| = 2^20 = 1048576`, `k = 2^19 = 524288`, `k+1 = 524289`)

All three radii satisfy the hypothesis `k + 2e ≤ n` (`e ≤ 2^18`); `e = n/4` is the boundary.

| `e` | `B(e) = (k+1)e + 1` | certified `log₂B` interval | `m_min = ⌈128 + log₂B⌉` | `B ≤ 2^(m_min−128)` |
|---|---|---|---|---|
| `⌊n/6⌋ = 174762` | `91 625 794 219` | `(36, 37)`, i.e. `2^36 < B < 2^37` | `165` | `B ≤ 2^37 = 137 438 953 472` ✓ |
| `⌊n/5⌋ = 209715` | `109 951 267 636` | `(36, 37)` | `165` | `B ≤ 2^37` ✓ |
| `n/4 = 262144` | `137 439 215 617` | `(37, 38)` | `166` | `B ≤ 2^38` ✓ (exceeds `2^37` by `262 145`) |

## 3. Field thresholds (target `ε_mca ≤ 2^−128`, criterion `B(e) ≤ 2^(m−128)`)

| `e` | `m_min` | `2^146` | `2^160` | `2^192` | `2^256` |
|---|---|---|---|---|---|
| `⌊n/6⌋` | 165 | FAIL | FAIL | PASS | PASS |
| `⌊n/5⌋` | 165 | FAIL | FAIL | PASS | PASS |
| `n/4`   | 166 | FAIL | FAIL | PASS | PASS |

Exact separating threshold: `m ≥ 165` for `e ∈ {⌊n/6⌋, ⌊n/5⌋}`, `m ≥ 166` for `e = n/4`
(`m = 164`, resp. `165`, already fails).

## 4. Comparability table

| Bound | Declaration | Exact hypotheses | Domain vs. new theorem | Verdict at `n=2^20,k=2^19` |
|---|---|---|---|---|
| `#Bad ≤ max(C(n,e), e)` | `OrdinaryRSProximity.card_badSet_le_choose_radius` | `1 ≤ k`, `k ≤ n`, `2e + k ≤ n` | **SAME DOMAIN** | new theorem far **better**: `m_min` 165/166 vs `128 + ⌈log₂C(n,e)⌉ = 681 715 / 757 115 / 850 805` |
| `#Bad ≤ e + 1` (counting) | `SyndromeRigidity.card_badSet_le_succ` | `1 ≤ k`, `k + 3e ≤ n` | **STRICTLY NARROWER** (`e ≤ (n−k)/3 = 174762`) | stronger numerically (`m_min = 146`) but requires the extra hypothesis `k + 3e ≤ n`; applies only to `e = ⌊n/6⌋` of the three |
| `#Bad ≤ e + 1` (unique dec.) | `UniqueDecodingMCA.card_badSet_le_succ_radius` | `1 ≤ k`, `k ≤ n`, `3e < n − k + 1` | **STRICTLY NARROWER** (same window) | idem; this is the route behind `epsMCAmax_le_rho_half_counting` (field `2^146`) |
| `#Bad ≤ e + 1` (pencil) | `WelchBerlekampPencil.card_badSet_le_of_wbDet_ne_zero` | `1 ≤ k`, `∃ρ, wbDet k e f₀ f₁ ρ ≠ 0` | **STRICTLY DIFFERENT** (structural, no radius condition) | stronger numerically (`m_min = 146`) but requires a nonvanishing maximal minor; it is exactly the first branch consumed inside the new proof |
| `#Bad ≤ e` (correlated) | `CorrelatedCommonSupport.card_badSet_le_of_correlatedAgreement` | `1 ≤ k`, `k + 2e ≤ n`, `∃ q₀,q₁`, `deg qᵢ < k`, `|A(f₀,q₀) ∩ A(f₁,q₁)| ≥ n − e` | **STRICTLY NARROWER** (conditional on the conclusion of correlated agreement) | see 3A |
| `#Bad ≤ e` (zero branch) | `Subresultant.card_badSet_le_of_W_can_eq_zero` | `1 ≤ k`, `k + 2e ≤ n`, `KernelNonzero k e f₀ f₁`, `W_can = 0` | **STRICTLY NARROWER** | see 3A |
| `#Bad ≤ (k+1)e + 1` (dichotomy) | `Subresultant.card_badSet_le_dichotomy` | `1 ≤ k`, `k + 2e ≤ n`, `KernelNonzero` | **STRICTLY NARROWER** | equal numerically; the kernel hypothesis is *not* automatic (`kernelNonzero_not_automatic`), so the new theorem strictly enlarges the domain |
| `#Bad ≤ n` | `MCA.card_badSet_le` | `1 ≤ k`, `k ≤ n`, `3e < n − k + 1` | STRICTLY NARROWER | dominated by the `e+1` bounds; `n = 2^20`, `m_min = 148` |
| `#Bad · C(T−1,a−1) ≤ C(n,a)` | `CircuitIncidence.card_badSet_le_circuit` / `…_le_choose` | `k+1 ≤ a ≤ max(n−e, k+1)` (no radius condition) | STRICTLY DIFFERENT (also covers `e > (n−k)/2`) | at `δ ≈ 0.3` it is the only option, at cost `2^699180` (`epsMCAmax_le_rho_half_circuit`); inside `k+2e ≤ n` the new theorem is better by ~`10^5` bits |

**3A — correlated branch.** Valid only under: `1 ≤ k`, `k + 2e ≤ n`, and *either* an explicit
pair `q₀,q₁` of degree `< k` whose common agreement set has size `≥ n − e`, *or*
(`Subresultant` form) `KernelNonzero k e f₀ f₁` together with `W_can k e f₀ f₁ = 0`.
Numerical gain: `#Bad ≤ e` instead of `(k+1)e + 1`, i.e. a factor `≈ k+1 = 2^19`;
`m_min` drops from 165/165/166 to `146` for all three radii. Logical price: the hypothesis is
the correlated-agreement statement itself (circular for soundness use), or a nonvanishing
Welch–Berlekamp kernel, which by `Subresultant.kernelNonzero_not_automatic` does **not** follow
from `1 ≤ k` and `k + 2e ≤ n`.

**3B — same-domain bounds.** The only bound with logically identical hypotheses is
`card_badSet_le_choose_radius`; against it the new theorem is **better** (by ~681 550 bits of
field size at `e = ⌊n/6⌋`). No same-domain bound is equal or better. All `e + 1` and `e`
bounds are strictly narrower: stronger numerically, but require the additional hypothesis
`k + 3e ≤ n`, or a nonzero WB minor, or correlated agreement itself.

## 5. Decision

**PRACTICAL: P-B** — sufficient only for large fields. At `n = 2^20`, `k = 2^19` the theorem
needs `|F| ≥ 2^165` (`e ≤ ⌊n/5⌋`) resp. `2^166` (`e = n/4`) for `ε_mca ≤ 2^−128`: `2^146` and
`2^160` FAIL, `2^192` and `2^256` PASS. At the small radius `e = ⌊n/6⌋` the pre-existing
`e + 1` route already reaches `2^146`, so the new theorem is practically relevant precisely in
the window `(n−k)/3 < e ≤ (n−k)/2`, where it turns an unusable `2^681715`-size requirement into
`2^165`.

**MATHEMATICAL: M-A** — quantitatively competitive with (in fact strictly better than) the best
comparable project bound: on its exact domain (`1 ≤ k`, `k + 2e ≤ n`, no structure) the only
logically comparable predecessor is `max(C(n,e), e)`, which it beats by ~10^5 bits; and it
removes the `KernelNonzero` hypothesis of `card_badSet_le_dichotomy` at no numerical cost.
It is not M-C: no theorem with identical hypotheses dominates it.
