# TWO-SYNDROME GATE — report

Mission: decide, using the **actual repository MCA definitions**, whether two distinct bad
challenges / witnesses naturally produce two syndrome sequences

```
S⁽¹⁾_r = ∑_{x ∈ E₁} v⁽¹⁾_x xʳ ,      S⁽²⁾_r = ∑_{x ∈ E₂} v⁽²⁾_x xʳ
```

with a **useful common support**, so that an `s = 2` simultaneous (interleaved-RS /
partial-inverse) locator recovery could be run inside the MCA proof.

New Lean file: `RequestProject/Root/CodingTheory/TwoSyndromeGate.lean` (sorry-free, built,
imported and axiom-audited in `RequestProject/Main.lean`; axioms of every listed declaration are
`[propext, Classical.choice, Quot.sound]`).
Exact probes: `analysis/two_syndrome_gate_probe.py` (+ `_output.txt`),
`analysis/two_syndrome_gate_pi_failures.py` (+ `_output.txt`).

---

## RETURN BLOCK

**TWO NATURAL CHANNELS: YES** (exactly two, and provably never more).

**SOURCE.** `Root.CodingTheory.rsSyndrome` applied to the line `lineComb f₀ f₁ γ = f₀ + γ·f₁`
of `MCA.lean`.  `rsSyndrome_lineComb` (already in `SyndromeSpace.lean`) gives
`H(f₀ + γ f₁) = A + γ·B` with `A = H f₀`, `B = H f₁`.  New, machine-checked:

* `channel_affine_combination` — for `z₁ ≠ z₂` and **any** `z`,
  `H(f₀+z f₁) = ((z₂−z)/(z₂−z₁))·H(f₀+z₁f₁) + ((z−z₁)/(z₂−z₁))·H(f₀+z₂f₁)`;
* `channelSpan_eq_span_pair` — `span { H(f₀+z f₁) : z ∈ F } = span { H f₀, H f₁ }`.

So the entire family of "MCA channels" **is** the interleaved pair `(f₀,f₁)`: `s = 2` is
available and simultaneously maximal, and a third bad challenge is exactly redundant
(kill-condition 3 of the mission, in provable form).

**EXACT FORMULAS.**  With the GRS dual multipliers `λ_x = ∏_{y≠x}(x−y)⁻¹` and
`r = 0 … n−k−1`:

```
S⁽¹⁾_r = ∑_{x∈D} f₀(x) λ_x xʳ = ∑_{x∈E} a(x) λ_x xʳ ,     a = f₀ − q₀
S⁽²⁾_r = ∑_{x∈D} f₁(x) λ_x xʳ = ∑_{x∈E} b(x) λ_x xʳ ,     b = f₁ − q₁
S^{(γ)}_r = S⁽¹⁾_r + γ S⁽²⁾_r  = ∑_{x∈E_γ} (a(x)+γ b(x)) λ_x xʳ ,
E_γ = { x ∈ E : a(x) + γ·b(x) ≠ 0 } ,     E = jointSupport a b = { x : a(x)≠0 ∨ b(x)≠0 }.
```

**COMMON SUPPORT: REDUCIBLE ONLY TO THE UNION** — never `E₁ = E₂`.

* `badWitness_ne`: two distinct bad challenges can **never** share a witness set `S`.  (One line
  from the existing small-union rigidity `lineCloseOn_of_two_close_on`: if two line points are
  close on the same `S`, the whole line is, contradicting badness.)
* `eq_zero_of_two_cancellations`: `a+z₁b = 0 = a+z₂b`, `z₁≠z₂` ⇒ `a = b = 0`.  Badness of `γ` is
  precisely a *cancellation* event on `E`, and cancellation sets of distinct challenges are
  disjoint; hence `channelSupport_ne_of_cancels`: `E₁ ≠ E₂` always, and `E₁ ∩ E₂` can be empty.
* `jointSupport_eq_union`: `E₁ ∪ E₂ = E` — the union is the *only* canonical common support, and
  `|E| ≤ 2e`, which is exactly the radius already delivered for free by the existing two-point
  result `exists_correlatedAgreement_of_two_goodZ` (no decoding involved).
* `exists_correlatedPair_of_commonSupport`: if two distinct channels *did* share a support `E`,
  then `f₀,f₁` agree with codewords off `E` — obtained by inverting a `2×2` system.  A genuine
  common support **is** the correlated-agreement conclusion, not a decoder input.  The proposed
  route is therefore circular in its success branch.

**STACKING ADDS RANK: YES, but on the wrong object.**  Exact tests: stacking increased the
Hankel rank in 106 977 / 107 010 of the pairs with a nonempty stacked system.  The object being
located is however the **union** `E₁ ∪ E₂` of size up to `2e`, not a size-`e` support.  Budget
(`twoChannelBudget_iff`): `m+1 ≤ 2(n−k−m) ⟺ 3m+1 ≤ 2(n−k)`.  With `m = 2e` and rate `1/2`,
`twoChannel_rate_half_threshold` gives

```
6e < n ,   i.e.  δ < 1/6 ,
```

*below* the `δ = 1/4` baseline, never mind `δ_J^safe ≈ 0.291916`.  The pre-screen in the mission
compared `e` with `⅔(n−k)`; the correct comparison is `2e` with `⅔(n−k)`.  At both project
schedules the stacked system is not merely tight but **empty**:

| schedule | `n−k` | union `2e` | rows/channel `n−k−2e` |
|---|---|---|---|
| defect-2, `e = 262145` | 524288 | 524290 | 0 (`defectTwo_stacked_system_empty`) |
| safe Johnson, `e = 306096` | 524288 | 612192 | 0 (`safeJohnson_stacked_system_empty`) |

**PI SUCCESS RATE IN EXACT TESTS.**  3 364 267 genuine bad-challenge pairs from FULL-MCA
instances (exhaustive over all word pairs for `GF(3), |D|=3` and `GF(5), |D|=4`; 4000 random word
pairs per parameter set for `GF(7), |D|=5`, `GF(11), |D|=6`, `GF(13), |D|=7`; `k ∈ {1,2}`,
`e ∈ {1,2,3}`; challenges, witnesses and closeness computed by full enumeration of all degree-`<k`
polynomials, no sampling of the semantics):

* `E₁ = E₂`: **0 / 3 364 267**;
* `E₁ ∩ E₂ = ∅`: 1 940 608;
* `span{S^{(γ₁)},S^{(γ₂)}} = span{H f₀, H f₁}`: 3 364 267 / 3 364 267;
* `|E₁ ∪ E₂| = 2e` (worst-case doubling attained): 1 486 562;
* stacked system **empty** (`|E₁∪E₂| ≥ n−k`): 3 257 257 (96.8 %);
* among the 107 010 pairs with a nonempty system: stacking adds rank 106 977; PI success
  (true locator = unique minimal simultaneous solution) **97 201 / 107 010 ≈ 90.8 %**, and
  97 207 pairs satisfy the budget — i.e. PI success ⟺ budget, up to 6 exceptions.

**PI FAILURE CERTIFICATE.**  Inside the budget there are exactly 6 failures in the whole exact
range, all of one shape: the stacked block-Hankel matrix is **rank-deficient by one**,

```
rank ( H⁽¹⁾ ; H⁽²⁾ ) = m − 1 < m ,       dim ker = 2 ,
```

with `m = |E₁ ∪ E₂|` (one distinct word pair, six challenge pairs), i.e. *every* maximal
`m × m` minor of the stacked system vanishes while the
error-value matrix `(v⁽¹⁾_x ; v⁽²⁾_x)_{x∈E}` still has rank 2 — confirming the mission's warning
that global row rank is not the right certificate.  Witness (`GF(13)`, `n = 7`, `k = 1`,
`e = 3`): `f₀ = (7,9,11,7,10,7,6)`, `f₁ = (11,4,8,11,4,11,6)`, `γ ∈ {4,5}`, `E₁ = {2,4,6}`,
`E₂ = {1,2,4}`, union `{1,2,4,6}`, 2 rows/channel, `rank H⁽¹⁾ = 2`, `rank` stacked `= 3`,
`dim ker = 2`.  This certificate is recorded for completeness only; it is not load-bearing,
because the route dies earlier, on the radius arithmetic.

**PI FAILURE + UNSTRUCTURED FOUND: NO** (and not decisive) — the 6 in-budget failures all come
from a single exact word pair (the `GF(13)` instance above, several challenge pairs), at
`δ = e/n = 3/7 ≈ 0.43`; the route is killed by the support/radius gate long before the failure
classification matters, so no attempt was made to match these against the existing
explaining-pair / large-`T` / curve-line / annihilator structure.

**SMALLEST EXACT COUNTEREXAMPLE** (formalised, `GateCounterexample`): `F = GF(3)`, `D = F`,
`n = 3`, `k = 1`, `e = 1`, `f₀ = (0,0,1)`, `f₁ = (0,1,0)`.  Both `γ = 0` (`isBad_zero`) and
`γ = 1` (`isBad_one`) are bad; their channel error supports are `{2}` and `{0}` —
**disjoint** (`channel_supports_disjoint`, `channel_supports_ne`); the union has size
`2 = 2e = n − k` (`union_card`), so the stacked `s = 2` system has `0` rows
(`stacked_rows_zero`).

**DECISION: KILL.**

Reasons, in order of strength:

1. `E₁ = E₂` is impossible (`badWitness_ne`, `channelSupport_ne_of_cancels`) — the gate's
   hypothesis never holds;
2. the only canonical common support is the union, of size up to `2e`, and the `s = 2` budget for
   it forces `δ < 1/6` at rate `1/2` — worse than the existing `δ = 1/4` baseline, and at both
   project schedules the stacked system has zero equations;
3. the success branch is circular: a genuine size-`e` common support already **is** correlated
   agreement (`exists_correlatedPair_of_commonSupport`), so nothing would be gained by decoding
   it;
4. no third channel exists: all challenge syndromes live in `span{H f₀, H f₁}`
   (`channelSpan_eq_span_pair`), so the route cannot be repaired by raising the interleaving
   order `s` — the extra channels that interleaved-RS theory would need simply are not present in
   MCA data.

Per the mission's own kill instruction, the programme returns to `GapBound`.

**NEXT SINGLE LEMMA** (not the simultaneous-locator lemma, which is now pointless).  The kill
isolates one quantity as the real obstruction: *the overlap of the channel supports*.  Everything
would change if one could prove, for two bad challenges of a line at radius `e`,

```
|E₁ ∩ E₂| ≥ (1 − c)·e     for some c < 1  ⟹  |E₁ ∪ E₂| ≤ (1 + c)·e ,
```

since the union radius, not `e`, is what the `s = 2` budget must accommodate (`δ < (1−ρ)/(3(1+c)/2)`
after substitution).  The exact tests say this is false in general (58 % of the observed pairs
have `E₁ ∩ E₂ = ∅`), so the lemma to attempt next is its conditional form: *under the existing
`johnson_escape_or_structure` explaining-pair hypothesis*, does the explaining pair force
`|E₁ ∩ E₂|` to be large, or does small overlap already produce a structure certificate?  That is
a statement about the existing structure branch, not about interleaved decoding — and it is the
only surviving way the two-channel idea could re-enter.

---

## Declarations added

`RequestProject/Root/CodingTheory/TwoSyndromeGate.lean`:

```
Root.CodingTheory.Syndrome.syndromeLine_affine_combination
Root.CodingTheory.channel_affine_combination
Root.CodingTheory.channel_mem_span_pair
Root.CodingTheory.channelSpan_eq_span_pair
Root.CodingTheory.not_isCloseOn_of_not_lineCloseOn
Root.CodingTheory.badWitness_ne
Root.CodingTheory.exists_correlatedPair_of_commonSupport
Root.CodingTheory.eq_zero_of_two_cancellations
Root.CodingTheory.channelSupport            (definition)
Root.CodingTheory.jointSupport              (definition)
Root.CodingTheory.channelSupport_subset_jointSupport
Root.CodingTheory.jointSupport_eq_union
Root.CodingTheory.channelSupport_ne_of_cancels
Root.CodingTheory.twoChannelBudget          (definition)
Root.CodingTheory.twoChannelBudget_iff
Root.CodingTheory.twoChannel_rate_half_threshold
Root.CodingTheory.defectTwo_stacked_system_empty
Root.CodingTheory.safeJohnson_stacked_system_empty
Root.CodingTheory.twoChannel_max_radius_rate_half
Root.CodingTheory.GateCounterexample.isBad_zero
Root.CodingTheory.GateCounterexample.isBad_one
Root.CodingTheory.GateCounterexample.channel_supports_disjoint
Root.CodingTheory.GateCounterexample.channel_supports_ne
Root.CodingTheory.GateCounterexample.union_card
Root.CodingTheory.GateCounterexample.stacked_rows_zero
```

No new axioms, no `sorry`, and no existing declaration was modified.
