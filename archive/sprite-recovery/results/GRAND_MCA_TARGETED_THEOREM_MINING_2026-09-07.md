# TARGETED THEOREM MINING — 2026-09-07

This is a bounded search for the current proof spine only. It is not a new MCA
route and it does not certify any external theorem for the deployed predicate.

## Ranked candidates

Scores are ordinal: semantic match * quantitative strength * downstream power /
formalization cost, each factor on a 1--5 scale.

1. Exact PG(2,p) incidence algebra
   Source pattern: finite projective-plane incidence matrix; A A^T = p I + J,
   Levi eigenvalues ±(p+1), ±sqrt(p).
   Confidence 5, cost 1, semantic match 5, strength 2, downstream 3, score 30.
   Value: cheap exact adapter; converts conflict energy to average/variance.
   Limitation: does not by itself force a quotient-visible heavy pencil.

2. Higher-dimensional agreement testing / local-to-global maps
   Source: Agreement Tests on Graphs and Hypergraphs,
   https://epubs.siam.org/doi/10.1137/21M1397684
   Confidence 4, cost 4, semantic match 4, strength 4, downstream 5, score 20.
   Pattern: pairwise overlap agreement plus reverse-union/majority decoding gives
   a global object on most local pieces.
   Limitation: sampling model, local objects, and exact projective-pencil
   distribution do not yet match; use only as a template.

3. Grassmann agreement testing
   Source pattern: Grassmann agreement test, Theory of Computing 2025.
   Confidence 4, cost 4, semantic match 4, strength 4, downstream 4, score 16.
   Limitation: exact constants and coefficient-field/section semantics require
   extraction from the paper; not an imported theorem.

4. Scattered linear sets on a projective line
   Source:
   https://www.sciencedirect.com/science/article/pii/S1071579715000076
   Confidence 4, cost 3, semantic match 4, strength 3, downstream 4, score 16.
   Value: exact rank/weight/fibre vocabulary for rank-2 quotient loci.
   Limitation: no direct deployed bound without a translation lemma.

5. Expander-mixing for finite projective planes
   Source pattern:
   https://anuragbishnoi.wordpress.com/2017/04/02/expander-mixing-lemma-in-finite-geometry/
   Confidence 5, cost 1, semantic match 3, strength 2, downstream 3, score 18.
   Value: exact spectral control for incidence edge distribution.
   Limitation: only average concentration; cannot replace the conflict
   concentration theorem.

6. Gain-graph balance/frustration
   Source:
   https://doi.org/10.1016/j.ejc.2008.02.004
   Confidence 4, cost 3, semantic match 3, strength 2, downstream 3, score 8.
   Value: language for section disagreements and balanced subgraphs.
   Limitation: generic gain graphs do not encode the K/F_p quotient or same-support
   semantics; no direct cardinal improvement.

7. Balanced-subgraph lower bound
   Pattern: every connected signed graph has a balanced subgraph with at least
   m/2+(n-1)/4 edges.
   Confidence 5, cost 2, semantic match 2, strength 2, downstream 2, score 10.
   Limitation: too weak and wrong graph model for the required quotient-visible
   family.

8. Finite-field bilinear fibre counting
   Generic rank/fibre theorem pattern.
   Confidence 5, cost 2, semantic match 4, strength 3, downstream 4, score 24.
   Value: likely the best local lemma for Rank2QuotientFunctionalDescent.
   Limitation: must be specialized to the actual multiplication tensor; no
   external theorem imported here.

9. Rank-one matrix/projective-line normalization
   Pattern: rank-one families parameterized by PG(1,p).
   Confidence 5, cost 2, semantic match 4, strength 3, downstream 4, score 24.
   Value: canonical chart/fibre proof and exact M accounting.
   Limitation: adapter only; does not establish concentration.

10. Prove2Me affine collision/fibre bounds
    Source pages are listed in external_reuse/prove2me.
    Confidence 2, cost 3, semantic match 3, strength 2, downstream 3, score 6.
    Limitation: visible sorry snippets and prime-ZMod hypotheses; local replay
    required before any use.

## Selected top three for immediate reuse

A. PG(2,p) incidence adapter.
B. Agreement-testing/local-to-global pattern, with exact hypotheses extracted
   before formalization.
C. Bilinear rank-2 fibre/projective-line adapter.

No candidate is treated as a proof of the official same-support theorem.

## Hidden duplication found

- formal/GrandMCA/CanonicalRankChart.lean already contains a projective-fibre
  field; Rank2QuotientAdapter is an interface specification, not a second
  theorem.
- Existing results already contain determinantal singleton-locus and rank-2
  obstruction analyses; do not reopen locator or raw quotient-energy routes.
- Existing Bilinear Functional Descent program already records rank-2 chart and
  fibre obligations; the new handoff only extracts the exact numerical target.
- The current state already records the external-coordinate FunctionalDescent
  mismatch; it remains the single semantic warning for any external theorem.

