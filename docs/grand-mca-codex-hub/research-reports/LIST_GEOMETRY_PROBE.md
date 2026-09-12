# List-geometry probe: which invariant of the nearby-codeword list controls `#Bad`?

Exploratory report for the "list geometry" mission.  Script:
`analysis/list_geometry_probe.py`, saved output `analysis/list_geometry_probe_output.txt`
(exact integer arithmetic over prime fields; instances enumerated over coset representatives,
which is exhaustive up to the proved invariance `badSet_sub_codeword`).  The follow-up
charging experiment and the full falsification hierarchy are in `GEOMETRIC_CHARGING_AUDIT.md`.

Notation: `C` a Reed–Solomon code, `n = |ι|`, `d = d(C)`, radius `e`, line `γ ↦ f₀ + γ f₁`,
`w = d(f₁,C)`, `L = L(f₁,2e) = {q ∈ C : d(f₁,q) ≤ 2e}`, `#Bad = |badSet C e f₀ f₁|`.
All instances are in the **gap** `¬(2e < w) ∧ ¬(2e + 2w < d)`, where the previously proved
theorems say nothing.

## Why radius `2e` is the right list radius

If `γ ≠ γ'` are bad with witnesses `(S,c)`, `(S',c')`, then on `S ∩ S'` (size `≥ n − 2e`)
`(γ−γ')f₁ = c − c'`, so the secant slope `(γ−γ')⁻¹(c−c')` is a codeword within `2e` of `f₁`.
Measured: **2 092 secant slopes over three RS families, 0 outside `L(f₁,2e)`** — and this is now
a Lean theorem (`Alphabet.hammingDistance_slope_le`), so the experiment only confirms it.

## Candidate invariants, 2 714 gap instances

| candidate | violations |
|---|---|
| C1 `#Bad ≤ max(1, n − max_{i<j}|Z(qᵢ−q_j)|)` (pairwise zero loci) | 994 |
| C3 `#Bad ≤ max(1, 2e·dim W)`, `W = span(L − q₀)` | 40 |
| C5 `#Bad ≤ max(1, |L|)` | 40 |
| C4 `#Bad ≤ max(1, 2e·dim span{f₁ − q : q ∈ L})` (syndrome span) | 0 (but see below) |
| C5b `#Bad ≤ max(1, 2e·|L|)` | 0 |
| C7 `#Bad ≤ 1 + |L|(2e−1)` | 0 |
| C6 `#Bad ≤ 1 + Σ_{q∈L}(d(f₁,q) − 1)` | 0 |
| **C8 `#Bad ≤ max(1, Σ_{q∈L} d(f₁,q))`** (strongest survivor for `|L| ≥ 2`) | 0 |
| old row `#Bad ≤ max(1, w)` | 1 323 |

Discriminating tests (same `(p, n, d, e, w)`, different `#Bad`) showed that neither `dim W`, nor
the pairwise zero loci, nor their intersections, nor the syndrome dimension separate a low from a
high `#Bad`: within such a bucket these invariants are constant while `#Bad` ranges over
`{1,…,7}`.  Only the list-weight quantities move with `#Bad`.  So the pairwise/zero-locus route
is dead, and the syndrome-dimension candidate C4, although unviolated here, is **not** adopted:
its right-hand side is bounded by `2e(k+1)` independently of `|F|`, and the adversarial search
that was run (RS`[4,2]` over `F₁₁`, `F₁₃`, `F₁₇`) neither refuted nor supported it beyond
`#Bad ≤ 4`; it remains an open, untrusted conjecture.

## Outcome

C8 is the surviving invariant, and it is now **proved in Lean**, as the counting corollary
of the charging map:

```
Alphabet.card_badSet_le_sum_hammingDistance :
  (∀ q ∈ C, d(f₁,q) ≤ 2e → q ∈ Q)  →  #Bad ≤ max 1 (∑ q ∈ Q, d(f₁,q))
```

unconditionally — no minimum distance, no hypothesis on the second layer, and for an arbitrary
linear code over a module alphabet, not just Reed–Solomon.  See `GEOMETRIC_CHARGING_AUDIT.md`
for the structural statement behind it and for the minimal counterexamples that kill the
alternative invariants (nearest-codeword, radius, boundary/branching mass).

## Follow-up

The next round — a *capacity* refinement of the same charging mechanism (a nearby codeword can
absorb at most `e + 1`, and often only `2`, bad parameters), together with the exact localisation
of the remaining obstacle (the number of *achieved* slopes) — is in `LIST_GEOMETRY_FRONTIER.md`,
with Lean proofs in `RequestProject/Root/CodingTheory/ChargingCapacity.lean`.
