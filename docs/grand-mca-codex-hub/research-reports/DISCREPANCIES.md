# Discrepancy and trust table

This document is the mandatory honesty artifact of the project. Every item is placed in
exactly one of four categories, and **no item is moved between categories without a
proof**:

* **P — proved in Lean.** Machine-checked, `sorry`-free, no added axioms
  (`RequestProject/Main.lean` prints the axiom audit; only `propext`,
  `Classical.choice`, `Quot.sound` occur).
* **I — implemented, not verified.** Code or contracts that exist in the repository but
  were not checked by a tool in this environment.
* **A — assumed.** Something the implementation relies on and that is *not* proved here.
* **O — open / not formalised.** Stated as a question, with a decision criterion.

Nothing in this repository was benchmarked. **No performance claim relative to any
existing library is made anywhere**, and none may be derived from the cost theorems:
those are statements in an explicitly defined operation-count model, not measurements.

---

## 1. Proved in Lean (P)

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P1 | `2³¹ − 1` is prime | `FFT.mersenne31_prime` | `M31Basic.lean` |
| P2 | Multiplication by `2^k` mod `2ⁿ−1` is a bit rotation of the canonical representative, already reduced | `FFT.mul_two_pow_mod_mersenne` | `M31Basic.lean` |
| P3 | `M31` has no primitive `2^k`-th root of unity for `k ≥ 2` (negative result) | `FFT.M31.no_primitiveRoot_two_pow` | `M31Basic.lean` |
| P4 | `M31` has no primitive 30-th root of unity (negative result) | `FFT.M31.no_primitiveRoot_thirty` | `M31Basic.lean` |
| P5 | `𝔽_{p²}` has primitive `2^k`-th roots for all `k ≤ 32` | `FFT.M31sq.exists_primitiveRoot_two_pow` | `M31Ext.lean` |
| P6 | DFT inversion, matrix form, determinant, `K₁` class | `FFT.dft_dft_inv`, `FFT.det_dftMatrix`, `FFT.dftK1Class` | `DFT.lean` |
| P7 | Radix-2 Cooley–Tukey recursion computes the DFT; exact operation counts | `FFT.fftRec_eq_dft`, `FFT.fftMuls_eq`, `FFT.fftMulsOpt_eq` | `CooleyTukey.lean` |
| P8 | Bit reversal is an involution | `FFT.bitrev_bitrev` | `BitReversal.lean` |
| P9 | Length-31 kernel over `M31` with **0** field multiplications; correctness and overflow bound | `FFT.dft31_correct`, `FFT.dft31_no_overflow`, `FFT.dft31_program_cost` | `M31FFT.lean`, `OpCount.lean` |
| P10 | Rader's identity for length 31; the resulting length-30 cyclic convolution | `FFT.rader31`, `FFT.rader31_conv` | `M31FFT.lean`, `RaderConvolution.lean` |
| P11 | Circle group over `M31` is cyclic of order `2³¹`, explicit generator | `FFT.Circle.orderOf_gen`, `FFT.Circle.isCyclic_circle_M31` | `CircleGroup.lean` |
| P12 | **Machine-word layer**: `UInt32` kernels `add/sub/neg/mul` compute the field operations under the quasi-canonical invariant `QC` | `FFT.Machine.toF_add`, `toF_sub`, `toF_neg`, `toF_mul`, `QC_*` | `MachineM31.lean` |
| P13 | Branch-free (mask) variants coincide with the reference kernels | `FFT.Machine.addMask_eq_add`, `subMask_eq_sub` | `MachineM31.lean` |
| P14 | **Lazy reduction**: `k` additive levels keep values `< B·2^k`; with `B = 2³¹` up to 32 levels fit in `u64` | `FFT.Machine.lazy_levels_bound`, `lazy_levels_no_overflow` | `MachineM31.lean` |
| P14b | The butterfly recursion run in `UInt32` preserves `QC` and computes the field recursion; specialised to the circle FFT | `FFT.Machine.QC_mieval`, `FFT.Machine.toF_mieval`, `FFT.Machine.toF_mieval_circle` | `MachineButterfly.lean` |
| P15 | Generic butterfly tower: evaluation/interpolation mutually inverse, basis semantics, exact costs | `FFT.Tree.fwd_ieval`, `ieval_fwd`, `ieval_eq_sum`, `imulCount_eq` | `ButterflyTree.lean` |
| P16 | **Circle FFT over `M31`**: `cfft`/`icfft` mutually inverse on twin cosets of size `2^(m+1)`, `m ≤ 29` | `FFT.Circle.M31.cfft_correct` | `CircleFFT.lean` |
| P17 | Circle FFT semantics (low-degree extension in the circle-code basis) and exact cost | `FFT.Circle.icfft_eq_sum`, `FFT.Circle.cfft_cost` | `CircleFFT.lean` |
| P18 | **Free-twiddle theorem**: the number of general multiplications equals the number of twiddles outside `⟨2⟩`; zero for `m ∣ ord(2)`; over `M31` the mul-free lengths are exactly 1 and 31 | `FFT.Mersenne.mulCount_sumProg_eq`, `dft_mul_free`, `M31.mul_free_lengths` | `FreeTwiddles.lean` |
| P19 | **Good–Thomas / PFA**: with CRT indexing the DFT is a pure tensor product, no twiddles | `FFT.dft_pfa`, `FFT.dft_pfa_nested` | `GoodThomas.lean` |
| P20 | The `31·m` prime-factor combination step costs 0 multiplications, 31 rotations, 30 additions, and is correct | `FFT.pfa31_mulCount`, `pfa31_rotCount`, `pfa31_addCount`, `eval_pfa31` | `GoodThomas.lean` |
| P20b | **Split radix**: one decimation-in-frequency identity for every radix; exact determination of the `μ₄`-free twiddles; `S(k) < R(k)` for `k ≥ 4` in the twiddle-count model | `FFT.dft_dif`, `FFT.radix2_free_twiddles`, `FFT.split_radix_free_twiddles`, `FFT.splitRadixCost_lt_radix2Cost` | `SplitRadix.lean` |
| P21 | **Lower bound**: the multiplicative complexity of the length-2 cyclic convolution is exactly 2 | `FFT.SLP.cyclicConv2_optimal` | `SLPLowerBound.lean` |
| P21b | Karatsuba in a quadratic extension: 3 general multiplications (naive: 4), with a proved saving; and a general two-multiplication lower-bound criterion giving `2 ≤` for complex multiplication | `FFT.SLP.karatsubaProg_cost`, `karatsubaProg_correct`, `karatsuba_beats_naive`, `mul_lower_bound_two_of_delta`, `complexMul_lower_bound_two` | `Karatsuba.lean` |
| P22 | Kernel-checked test vectors (machine kernels, circle-FFT round trip, geometric LDE cross-check, PFA indexing, decimation-in-frequency indexing, Karatsuba vs naive) | `FFT.Reference.*` | `Reference.lean` |
| P23 | **Computable discrete logarithm**: bit-by-bit (Pohlig–Hellman) `dlog2` in any cyclic 2-group, proved correct and reduced; specialised to `C(M31)` it gives the explicit, computable isomorphism `Multiplicative (ZMod 2³¹) ≃* C(M31)` (`exp` by binary powering, `log` by `dlog2`), with kernel-checked test vectors | `FFT.dlog2_spec`, `FFT.Circle.pow_clog`, `FFT.Circle.clog_lt`, `FFT.Circle.clog_pow`, `FFT.Circle.zmodEquiv` | `CircleLog.lean` |
| P24 | **Short cyclic convolutions of length 3**: a 4-multiplication CRT/Karatsuba program over any field of characteristic ≠ 3, and a 3-multiplication program over a field containing a primitive cube root of unity (explicitly `1513477735` over `M31`), both with correctness proofs, exact multiplication counts and a kernel-checked test vector; plus a proved lower bound of 2 general multiplications | `FFT.SLP.cyclicConv3_prog_cost`, `cyclicConv3_prog_correct`, `cyclicConv3_omega_cost`, `cyclicConv3_omega_correct`, `cyclicConv3_lower_bound`, `FFT.M31Conv3.cyclicConv3_M31` | `WinogradConv3.lean` |
| P25b | **Bilinear model**: `p` linearly independent forms need `p` products; the bilinear complexity of the length-`n` cyclic convolution is exactly `n` whenever the field has a primitive `n`-th root of unity and `n ≠ 0` (over `M31`: exactly 3 for `n = 3`, exactly 31 for `n = 31`, where all linear forms are rotations) | `FFT.Bilinear.bilin_lower_bound`, `cyclicConv_bilinear_complexity`, `conv3_bilinear_optimal`, `cyclicConv31_M31_bilinear_complexity` | `BilinearLowerBound.lean` |
| P25c | **Bilinear model**: the complexity of multiplying polynomials of degrees `≤ m`, `≤ n` is exactly `m+n+1` over a field with `m+n+1` distinct elements (Toom–Cook attains it); in particular Karatsuba's 3 multiplications are optimal for two linear polynomials | `FFT.Bilinear.polyMul_bilinear_complexity`, `polyMul_M31_bilinear_complexity`, `karatsuba_bilinear_optimal` | `PolyMul.lean` |
| P25c2 | Folding the polynomial product modulo `xⁿ−1`: the length-`n` cyclic convolution has bilinear complexity between `n` and `2n−1` over any field with `2n−1` distinct elements; over `M31` the length-30 Rader convolution needs at least 30 and at most 59 general multiplications | `FFT.Bilinear.cyclicConv_bilinear_bounds`, `cyclicConv30_M31_bounds` | `PolyMul.lean` |
| P25d | `𝔽_{p^k}` has a primitive 30-th root of unity **iff** `4 ∣ k`; degree 4 is the minimal extension in which Rader's length-30 convolution can be evaluated by transforms | `FFT.M31.exists_primitiveRoot_thirty_ext_iff`, `FFT.M31.min_extension_degree_for_thirty` | `RaderThirty.lean` |
| P25e | **The DFT as an isomorphism of algebras** `F[C_n] ≃ₐ[F] (ℤ/n → F)` for `ζ` primitive of order `n` and `n` invertible (with the explicit inverse transform), hence the convolution theorem in algebra form, split semisimplicity of `F[C_n]`, and the **equivalence of categories** `Rep F C_n ≌ ModuleCat (ℤ/n → F)`; instantiated over `M31` at length 31 with `ζ = 2` | `FFT.dftAlgEquiv`, `FFT.dftAlgEquiv_mul`, `FFT.isSemisimpleRing_monoidAlgebra`, `FFT.repEquivPi`, `FFT.M31.dftAlgEquiv31`, `FFT.M31.repEquivPi31` | `GroupAlgebraDFT.lean` |
| P25f | **Agarwal–Cooley**: the bilinear model over an arbitrary finite group, with the `≥ \|G\|` lower bound, free relabelling, and the tensor product of algorithms; hence `c(mn) ≤ c(m)·c(n)` for coprime `m,n`, and over `M31` the length-30 Rader convolution in **54** products (`30 = 6·5`, improving the 59 of P25c2), still `≥ 30` | `FFT.Bilinear.ConvAlg.card_le_of_computes`, `tensor_computes`, `agarwalCooley`, `cyclicConv30_M31_agarwal_cooley` | `AgarwalCooley.lean` |
| P25g | **Isotypic decomposition**: for `T^n = 1` with `n` invertible and `ζ` primitive of order `n`, the DFT-weighted averages `S_j = ∑_{k<n} ζ^{−jk}T^k` satisfy `T∘S_j = ζ^j S_j` and `∑_j S_j = n`, hence `V = ⨁_{j<n} ker(T − ζ^j)` as an internal direct sum, naturally in `V`; over `M31` with `n = 31`, `ζ = 2` | `FFT.isoSum_eigen`, `FFT.sum_isoSum`, `FFT.cyclic_eigenspace_isInternal`, `FFT.mapsTo_eigenspace_of_comm`, `FFT.M31.cyclic31_eigenspace_isInternal` | `IsotypicDecomposition.lean` |
| P26 | **Cyclotomic coset counts over M31** (kernel-evaluated): `t(5)=2`, `t(6)=6`, `t(30)=12`, `t(31)=31`, hence the Winograd target `2·30 − t(30) = 48` for the length-30 Rader convolution | `FFT.Cosets.cosetCount_five`, `cosetCount_six`, `cosetCount_thirty`, `cosetCount_thirtyone`, `winograd_target_thirty` | `CyclotomicCosets.lean` |
| P27 | **Fiduccia–Zalcstein lower bound** in a coordinate-free bilinear model: if `x ↦ φ u x` is injective for every `u ≠ 0`, any bilinear algorithm for `φ` needs `≥ dim U + dim V − 1` products; hence multiplication in a `d`-dimensional domain needs `≥ 2d − 1`, and with the matching evaluation/interpolation algorithm the bilinear complexity of a field extension with a power basis and `2d − 1` points in the base field is **exactly `2d − 1`**; over `M31`: **exactly 3 for `𝔽_{p²}`** (the complex/Karatsuba kernel is optimal) and **exactly 7 for `𝔽_{p⁴}`** | `FFT.Bilinear.GenAlg.fiducciaZalcstein`, `domain_bilinear_lower_bound`, `powerBasisAlg_computes`, `ext_bilinear_complexity`, `M31sq_bilinear_complexity`, `M31quartic_bilinear_complexity` | `AlgebraRank.lean` |
| P28 | Correctness of a bilinear convolution algorithm reduces to a finite tensor identity (kernel-decidable over `M31`); explicit **8-product length-5** algorithm and hence the length-30 Rader convolution in **48** products (improving the 54 of P25f, matching the Winograd target of P26), still `≥ 30` | `FFT.Bilinear.ConvAlg.computes_of_tensor`, `exists_conv5_M31_eight`, `cyclicConv30_M31_48` | `Conv5.lean` |
| P29 | **Substitution method and the character lower bound**: `R(B × K) ≥ R(B) + 2 dim K − 1`, hence `t` jointly injective multiplicative characters into domains force `2 dim V − t` products; in algebra language the commutative Alder–Strassen bound `R(A) ≥ 2 dim A − t` | `FFT.Bilinear.substitution_bound`, `character_lower_bound`, `algebra_alder_strassen` | `Substitution.lean`, `CharacterBound.lean`, `ExactValues.lean` |
| P30 | **Winograd's lower bound `2n − t(n)` for cyclic convolution** (characters = evaluations at the `n`-th roots of unity, one per `p`-cyclotomic coset, joint injectivity via Frobenius), hence the **exact values over `M31`**: `c(5) = 8`, `c(6) = 6`, `c(10) = 16`, `c(15) = 24`, `c(30) = 48` | `FFT.Bilinear.convAlg_cyclotomic_lower_bound`, `cyclicConv5_M31_bilinear_complexity`, `cyclicConv6_…`, `cyclicConv10_…`, `cyclicConv15_…`, `cyclicConv30_M31_bilinear_complexity` | `WinogradLower.lean`, `ExactValues.lean` |
| P31 | **Exact complexity of split commutative algebras**: direct sums and transport of bilinear algorithms, the Chinese remainder algorithm `R(A) ≤ 2 dim A − t`, hence `R(A) = 2 dim A − t` for `A ≃ₐ[F] ∏ᵢ Kᵢ`, and — with no splitting supplied — for every finite-dimensional reduced commutative algebra over a finite field | `FFT.Bilinear.GenAlg.pi`, `GenAlg.congr`, `split_algebra_upper_bound`, `split_algebra_exact`, `reduced_algebra_exact` | `AlgebraSplit.lean` |
| P32 | **Winograd's theorem, exact form, for every length**: `c(n) = 2n − t(n)` over any finite field in which `n` is invertible (`t(n)` = number of maximal ideals of `F[x]/(xⁿ − 1)`), specialised to `M31` for every `n ≤ 2³⁰`; as a corollary the factor counts `t(5)=2`, `t(6)=6`, `t(10)=4`, `t(15)=6`, `t(30)=12` | `FFT.Bilinear.convComplexity_eq`, `convComplexity_M31_eq`, `factorCount_M31_five`, `factorCount_M31_thirty` | `ConvExact.lean` |
| P33 | **Recursive Toom–Cook with arbitrary integer evaluation points**: for every base `b > 1`, every `k_x, k_y ≥ 2` and every vector of pairwise distinct integer points `v⃗`, the full recursion (split into limbs → evaluate → recursive scalar products → Lagrange interpolation → recompose) returns `x·y` for all integers `x, y`; the recursion terminates by an explicit threshold `θ(b, k_x, k_y, v⃗)` that does not depend on the operands, together with the size-contraction lemma above `θ`; the classical Toom-3 points `⟨0,1,−1,2,−2⟩` and the unbalanced `k_x = 3, k_y = 2` are instances | `FFT.ToomCook.tk_THETA`, `tk_contraction`, `toomk`, `toomk_eq`, `toomk_correctness`, `toomkZ_correctness`, `toom3_correctness`, `toom32_correctness` | `ToomCook.lean` |
| P34 | **Iterative in-place radix-2 FFT**: the loop invariant of the butterfly passes (block `b` after pass `s` holds the length-`2^s` DFT of its bit-reversed contents), correctness of the whole in-place algorithm (bit-reversal swap loop + `k` passes = DFT), the disjointness facts that license in-place updates (the butterfly at `i` reads only `i` and `partner s i`; that map is a fixed-point-free involution), the index-range bound, the operation counts `k·2^(k−1)` / `k·2^k`, and the instantiation over `𝔽_{p²}` for every `2^k`, `k ≤ 32` | `FFT.InPlace.runStages_spec`, `iterFFT_eq_dft`, `bitrevSwaps_spec`, `inPlaceFFT_eq_dft`, `partner_involutive`, `partner_ne`, `stage_congr`, `stage_reads_lt`, `iterMuls_eq_fftMulsOpt`, `M31sq.exists_iterFFT_correct` | `InPlaceFFT.lean` |
| P25 | Linear-cost evaluation calculus for straight-line programs (one rewrite rule per instruction, side conditions discharged by `rfl`/`decide`), making programs of any length verifiable | `FFT.SLP.val_append_left`, `val_snoc`, `val_eq_step`, `val_inp/add/sub/smul/mul` | `SLPEval.lean` |
| P35 | **Package A**: the substitution step for an arbitrary finite-dimensional unital *associative* algebra (`R(R ⧸ I) < R(R)` for every nonzero two-sided ideal `I`), and the structural facts behind the restricted Bläser characterisation: `rad A = ⋂ maximal ideals`, `rad A` nilpotent, `A ⧸ rad A` semisimple, idempotents and complete orthogonal families of idempotents lift along `rad A`, `t(A) = t(A ⧸ rad A)` | `FFT.Bilinear.substitution_step`, `bilinRank_lt_of_proper_quotient`, `radical_eq_sInf_maximal`, `isNilpotent_radical`, `isSemisimpleRing_quotient_radical`, `exists_isIdempotentElem_lift`, `exists_completeOrthogonalIdempotents_lift`, `numMaxIdeals_quotient_radical` | `Substitution.lean`, `RadicalLift.lean` |
| P36 | **Package A, numerical part**: the ideal form of the substitution step (`R(A ⧸ I) < R(A)` and an algorithm of length `k − 1` for `A ⧸ I` whenever `I ≠ 0`), `dim (A ⧸ I) < dim A`, `t(A ⧸ I) ≤ t(A)`, `t(field) = 1`, and the equality case for a product (minimal rank of `A × B` ⟺ minimal rank of both factors, given the Alder–Strassen and peeling bounds) | `FFT.Bilinear.substitution_step_ideal`, `bilinRank_quotient_lt`, `finrank_quotient_lt`, `numMaxIdeals_quotient_le`, `numMaxIdeals_field`, `minimalRank_prod_iff_tight` | `RadicalLift.lean` |
| P37 | **Refutation**: the plan's proposed inequality `t(A ⧸ I) ≥ t(A) − 1` is false; machine-checked counterexample `A = 𝔽₂ × 𝔽₂ × 𝔽₂`, `I = ker(first projection)` (`t(A) = 3`, `t(A ⧸ I) = 1`). The true general statements are `t(A ⧸ I) ≤ t(A)` and `dim (A ⧸ I) < dim A` | `FFT.Bilinear.numMaxIdeals_quotient_not_ge` | `RadicalLift.lean` |

| P38 | **Root A — universal algebra**: signatures with arbitrary (possibly infinite) arities, terms, algebras, homomorphisms; the absolutely free algebra and its universal property; the free algebra of an equational theory, its congruence, its induction principle and its **universal property** `∃!` homomorphism extending an interpretation; the free algebra is a model of its axioms when the axioms are substitution-closed; quotients by congruences with their universal property; closure of equational classes under subalgebras, quotients and products (HSP) | `Root.Signature`, `Root.Term`, `Root.SigAlgebra`, `Root.IsSigHom`, `Root.evalTerm`, `Root.exists_unique_evalTerm`, `Root.FreeAlg`, `Root.FreeAlg.satisfies`, `Root.FreeAlg.exists_unique_lift`, `Root.free_alg_fold_unique`, `Root.SigCon.exists_unique_lift`, `Root.SigCon.satisfies`, `Root.SigSubalg.satisfies`, `Root.pi_satisfies` | `Root/Algebra.lean` |
| P39 | **Root A — instances and Mathlib bridge**: ring / commutative-ring / module signatures with substitution-closed axiom systems and the proofs that every ring, commutative ring and module is a model; `IsSigHom` between rings ⟺ ring homomorphism (both directions, with the bundled `RingHom` construction); the free ring on a set of generators and its universal property; R1CS constraints as pairs of ring terms with satisfaction ⟺ equality of term values and preserved by base change along a ring homomorphism; Plonk gates as single ring equations; AIR transition constraints as pairs of ring terms on consecutive trace rows, with base change preserving satisfaction; a bit-vector (ISA fragment) signature | `Root.Instances.RingOp`, `RingAx`, `CommRingAx`, `ring_satisfies`, `commRing_satisfies`, `ringAx_substClosed`, `commRingAx_substClosed`, `isSigHom_ring_iff`, `isSigHom_of_ringHom`, `ringHomOfIsSigHom`, `exists_unique_ring_lift`, `ModuleOp`, `module_satisfies`, `R1CS.sat_iff_evalTerm`, `R1CS.Constraint.sat_map`, `Plonk.sat_iff_evalTerm`, `AIR.sat_map`, `BitOp` | `Root/Instances.lean` |
| P40 | **Root A — integration of the existing modules**: `BilinAlg → GenAlg` with correctness preserved in both directions and the resulting transfer of the Fiduccia–Zalcstein bound to the coordinate model; an ideal of a commutative ring is a congruence for the ring signature, the universal-algebra quotient is canonically isomorphic to `R ⧸ I`, the comparison map is a homomorphism of signature algebras, and the universal property of `R ⧸ I` follows from the generic one | `FFT.Bilinear.BilinAlg.toGenAlg`, `toGenAlg_eval`, `toGenAlg_computes_iff`, `BilinAlg.fiducciaZalcstein`, `Root.Instances.conOfIdeal`, `quotEquivIdealQuotient`, `isSigHom_quotEquivIdealQuotient`, `exists_unique_lift_of_ideal` | `Root/Bridge.lean` |
| P41 | **Root A — limitation, proved**: fields are *not* an equational class over the ring signature — every axiom system satisfied by the field `ZMod 2` is satisfied by the product `Bool → ZMod 2`, which is not a field | `Root.Instances.field_not_equational` | `Root/Instances.lean` |
| P42 | **Root B — probability**: probability measures with `pure`/`bind` and the three monad laws (`bind` conditional on measurability of the kernel), the total-variation distance as a supremum over measurable sets with non-negativity, symmetry, `≤ 1`, the triangle inequality and the **data-processing inequality for deterministic post-processing**; finitely supported distributions with `pure`/`bind`, the monad laws, the total-variation distance, the **full data-processing inequality for Markov kernels**, and non-negativity of the Kullback–Leibler divergence (Gibbs) | `Root.Prob.pure_bind`, `bind_pure`, `bind_assoc`, `TV`, `TV_nonneg`, `TV_le_one`, `TV_comm`, `TV_triangle`, `TV_map_le`, `Root.FinProb.pure_bind`, `bind_pure`, `bind_assoc`, `tv_triangle`, `tv_bind_le`, `kl_nonneg` | `Root/Prob.lean` |
| P43 | **Root C — provability logic**: syntax and Kripke semantics of modal formulas; validity of `K` on all frames, of `4` on transitive frames and of the **Löb axiom on transitive, converse well-founded frames** (well-founded induction), together with a counter-model showing that converse well-foundedness cannot be dropped; the Hilbert–Bernays–Löb derivability conditions as a structure, **Löb's rule and Löb's theorem derived from them plus a Gödel fixed point**, and the corollary that a false `Box`-sound proposition admits no fixed point | `Root.Modal.valid_K`, `valid_four`, `valid_loeb`, `not_valid_loeb_reflexive`, `Root.Modal.Derivability`, `Derivability.loeb_rule`, `Derivability.loeb`, `Derivability.no_fix_of_not`, `derivability_id` | `Root/Modal.lean` |
| P44 | **Root D — coding theory**: Hamming metric (symmetry, triangle inequality, relative distance in `[0,1]`), linear codes as submodules and their minimum distance, unique decoding below half the minimum distance; Lagrange interpolation with uniqueness (`L1`), the bound on the number of zeros of a nonzero polynomial (`L2`) and the univariate Schwartz–Zippel lemma expressed with the probability layer of `Root/Prob.lean`; the Reed–Solomon code with **`d_min = |D| − k + 1`** | `Root.CodingTheory.hammingDistance`, `hammingDistance_triangle`, `minDistance`, `eq_of_lt_half_minDistance`, `existsUnique_interpolant`, `card_roots_in_le`, `schwartz_zippel`, `reedSolomonCode`, `reedSolomon_weight_ge`, `reedSolomon_minDistance`, `reedSolomon_unique_decoding` | `Root/CodingTheory/Hamming.lean`, `PolynomialInterpolation.lean`, `ReedSolomon.lean` |
| P45 | **Root D — local test and proximity gap (T1)**: the random-`s`-subset test, its acceptance probability `α(f)` and the proof that `α(f)` is a probability in the sense of `Root/Prob.lean`; the counting bound `#accepting ≤ C(n,k)·C(m,s)`; **T1**: `α(f) ≤ C(n,k)·C(m,s)/C(n,s)` whenever no polynomial of degree `< k` agrees with `f` on more than `m` positions; the contrapositive proximity gap (high acceptance ⇒ an explicit codeword within relative distance `< (n − m)/n`); sharpness `C(a,s)/C(n,s) ≤ α(f)`; the distance to the code (`Finset.min'`, no `sInf`) and `L3`; `L4` for affine lines together with completeness of the line test | `Root.CodingTheory.acceptProb`, `acceptProb_eq_probOf_uniform`, `card_goodSubsets_le`, `proximity_gap_subsets`, `proximity_gap`, `proximity_gap_distToCode`, `le_acceptProb_of_agreement`, `distToCode`, `exists_poly_dist_eq_distToCode`, `degree_comp_lineMap_lt`, `reedSolomon_restrict_line` | `Root/CodingTheory/LocalTests.lean`, `ProximityGapSubsets.lean`, `AffineSubspaces.lean` |
| P46 | **GG25 §4.2–4.3, pinned subspaces and the sharp bridge**: pinned subspaces `H_S` (GG25 Def. 4.4) and the unique-determination lemma; the deterministic core of the oblivious pruning algorithm `PRUNE_H` (every `H ≤ C` of dimension `≤ r` can be pinned to `0` by at most `r` coordinates taken from *any* prescribed agreement set, provided `e ≤ (1 − τ(r) − ε)n` and `r < εn`); the list-size bound that follows; the counting core with radius slack `(b−1)(n − e − |T|) ≤ e`; correlated agreement with slack and its folded-RS instantiation with the constant `(8/η² + 1)(2 + e/θ)` and the concrete threshold `\|F\| ≥ 2¹⁶²` for `2⁻¹²⁸` at `n = 2²⁰`, `η = 2⁻¹⁰`, `θ = 2¹⁰` | `Root.CodingTheory.Alphabet.pinnedSubspace`, `eq_of_agree_on_of_pinned_eq_bot`, `exists_coord_not_le_coordKer`, `exists_pinning_subset`, `exists_pinning_of_close`, `ncard_close_le_of_pinning`, `card_inter_agreement_ge_of_collinear_slack`, `SlackCorrelatedAgreement`, `slackCorrelatedAgreement_of_lineDecodable`, `slackCorrelatedAgreement_of_subspaceDesign`, `Root.CodingTheory.Folded.foldedRS_slackCA_gg25`, `foldedRS_slackCA_capacity`, `foldedRS_slackCA_two_pow_neg_128` | `Root/CodingTheory/PinnedSubspace.lean`, `Root/CodingTheory/SharpLineMCA.lean`, `Root/CodingTheory/FoldedRSSharp.lean` |
| P47 | **GG25 Theorem 3.6 and the literature constant for strong folded-RS MCA**: `ListDecodable` and the pair-collapse lemma `card_bigPairs_le_of_listDecodable` (`ListDecodable.lean`); the amplification theorem `lineDecodable_amplification`, turning a small collinearity count `t` into any count `b` at additive cost `L(b−1)` (`LineDecodableAmplification.lean`); the composed chain `epsMCAmax_le_of_subspaceDesign_listDecodable` (`SharpLineMCAAmplified.lean`); the literature constant `foldedRS_epsMCA_literature` (`ε_mca ≤ 2n/(η\|F\|) + 24/(η³\|F\|)`) and the threshold `foldedRS_threshold_2_158` (`n = 2²⁰`, `η = 2⁻¹⁰`, `\|F\| ≥ 26·2¹⁵⁸ ⇒ ε_mca ≤ 2⁻¹²⁸`), both for the **strong** notion `epsMCAmax`, both carrying the capacity list-decodability hypothesis of row O57; the unconditional Johnson-regime list-size bound `foldedRS_listDecodable_johnson` and the unconditional corollaries `foldedRS_epsMCAmax_amplified_uniqueDecoding`, `foldedRS_epsMCAmax_amplified_johnson` (`FoldedRSListDecodable.lean`, `FoldedRSMCAFinal.lean`) | see §47 of `RESULTS.md` |
| P48 | **Unconditional capacity list decoding of folded Reed–Solomon codes, and the resulting unconditional capacity-level strong MCA bound**: the abstract combinatorial core `singleton_bound` (average-radius *relaxed generalized Singleton bound* for affinely independent tuples, from the sharp design), `card_agree_le_succ_finrank`, the coset recursion `card_le_of_coset` and the assembled `listDecodable_of_design`, `listDecodable_of_design_top` (`CapacityListDecoding.lean`); the folded-RS instance `foldedRS_sharpDesign`, `foldedRS_capacity_listDecoding`, `foldedRS_capacity_listDecoding_ceil` (list size `capacityListSize ε = ⌈2/ε⌉^⌈2/ε⌉` at radius `1 − ρ − ε` for `s ≥ 16/ε² + 8/ε + 3`) and `foldedRS_capacity_listDecoding_exists` (`FoldedRSCapacityListDecoding.lean`); the budget arithmetic `amplified_budget_le_listSize` and the **hypothesis-free** bound `foldedRS_epsMCA_unconditional` : `ε_mca(C, e) ≤ (L·n + 24/η³)/\|F\|` for `e ≤ (1 − ρ − η)·n`, `L = ⌈4/η⌉^⌈4/η⌉`, plus `foldedRS_epsMCA_unconditional_exists` (`FoldedRSMCAUnconditional.lean`) | see §48 of `RESULTS.md` |
| P49 | **Srivastava amortisation: quadratic capacity list size.**  `card_le_of_coset_amortised`, `listDecodable_of_design_amortised` (`SrivastavaInduction.lean`); `card_le_of_coset_design`, `list_bound_two_budget`, `line_case_bound` (`SrivastavaAbstract.lean`); `capacityListSizeQuad`, `foldedRS_listDecoding_quadratic`, `foldedRS_listDecoding_quadratic_ceil` (`FoldedRSListDecodingImproved.lean`); `foldedRS_epsMCA_unconditional_quadratic` (`FoldedRSMCAQuadratic.lean`).  The requested abstract bound `(r−1)²+1` is **false** (repetition code over `F₃`, `n = 3`, `τ ≡ 0`, `r = 2`: a line carries 3 codewords at `δ = 2/3`); the corrected, tight bound `1 + d·r` is what is proved. | see §49 of `RESULTS.md` |

### Notes on the coding-theory request (Root D)

* The upper bound proposed for T1, `C(n − ⌊(1−δ)n⌋, s − k + 1)/C(n,s)`, is **not** what the
  argument of the request yields, and it is not a correct general upper bound (for `f` in
  the code the acceptance probability is `1`).  What is proved is the bound obtained from
  the union bound over the `C(n,k)` candidate interpolants,
  `α(f) ≤ C(n,k)·C(m,s)/C(n,s)` with `m` the largest agreement of `f` with a codeword
  (`Root.CodingTheory.proximity_gap_subsets`).
* Minimum distance is defined with `sInf` (as in the earlier request template) *and* the
  distance of a word to the code is defined with `Finset.min'` (as asked in the later
  request); both are proved to behave as expected.
* `Mathlib.Polynomial.natDegree_nroots_le` does not exist under that name in the pinned
  version; the zero-count bound is derived from `Polynomial.card_roots'`.

### Notes on the MCA (mutual correlated agreement) request

* The blueprint's Theorem M1 for the Johnson-radius rows is **not** proved here: the sketch
  supplied with it is not valid as written (it assumes the very line-closure property it is
  meant to establish).  Only the unique-decoding row is proved, and by a different, fully
  self-contained argument (`Root.CodingTheory.card_badSet_le`).
* `ε_pg ≤ ε_ca ≤ ε_mca` is *not* stated as an inequality between three separately defined
  quantities; instead the implication that carries the content is proved directly
  (`Root.CodingTheory.correlatedAgreement_of_epsMCA_lt`: a line whose random point is close
  with probability above `ε_mca` has a single common agreement set).
* The asymptotic threshold `δ* = 1 − √ρ` is recorded as open (O17); nothing here asserts it.

### Notes on the Guruswami–Sudan / Johnson-regime MCA work package (§28 of `RESULTS.md`)

* Bivariate polynomials are modelled as `F[X][X] = Polynomial (Polynomial F)` rather than
  `MvPolynomial (Fin 2) F`.  The requested `MvPolynomial` route was tried first; the
  univariate-over-univariate model makes substitution `Y := p(X)`, the degree bound on
  `Q(X, p(X))` and the factorisation `(Y − p) ∣ Q` direct consequences of the existing
  `Polynomial` API (`Polynomial.eval`, `Polynomial.dvd_iff_isRoot`, roots over `Frac F[X]`),
  whereas in `MvPolynomial` each of these steps has to be rebuilt.  Weighted degree
  (`GS.WdegLt`) and multiplicity (`GS.HasMultAt`, via the translation `GS.shiftBiv`, which is
  equivalent to the vanishing of all Hasse derivatives of order `< m` and is correct in
  characteristic `p`) are defined directly in this model.
* Hasse derivatives are therefore *not* defined explicitly; the translation-based definition
  requested as the alternative is used instead, and the multiplicity-to-divisibility step is
  proved from it (`GS.sub_pow_dvd_eval_of_hasMultAt`).
* The list-size bound is stated in the integer form `k·#S < m·t` under `k·n·(m+1) < m·t²`
  rather than as `#S ≤ L/k` with `L = ⌈√(2k n C(m+1,2))⌉ + 1`; the two are the same statement
  with `L = m·t`, and the integer form avoids real-valued ceilings inside the induction.
* The concrete instances are stated for the *exact* radii and field sizes computed in
  `analysis/mca_constants_check.py`, not for the round numbers of the request (see O22).

### Notes on the template code supplied with the Root request

The Lean snippets in the request do not compile as written; the following changes were
necessary, and each is documented in the corresponding file.

* `Root/Algebra.lean` — the class of algebras cannot be called `Algebra` (Mathlib's
  scalar-algebra class); it is `Root.SigAlgebra`.  The proposed
  `free_alg_fold_unique` is **false**: without requiring the map to be a homomorphism a
  function out of the free algebra is not determined by its values on the variables.  The
  proved statement adds that requirement.  The axiom family is a relation on terms over a
  fixed variable type, given in substitution-closed form; `Root.FreeAlg.satisfies` shows
  this is exactly what makes the free algebra a model of the axioms.
* `Root/Prob.lean` — `Measure.bind μ f` is a probability measure only when the kernel `f`
  is measurable, so `Prob.bind` carries that hypothesis and there is no unconditional
  `Monad` instance.  The data-processing inequality is proved for deterministic
  post-processing in the measure-theoretic layer and for arbitrary Markov kernels in the
  finite layer.
* `Root/Modal.lean` — `box_distrib`, `box_trans` and `lob` are **not** added as axioms
  (the project adds no axioms).  They appear as the fields of the `Derivability` structure
  (hypotheses) and as proved theorems: Löb's rule and Löb's theorem follow from the
  derivability conditions plus a Gödel fixed point, and the Löb schema is proved valid on
  transitive converse-well-founded Kripke frames.

## 2. Implemented but not verified in this environment (I)

| # | Item | Where | Why not verified |
| --- | --- | --- | --- |
| I1 | Verus contract skeleton for the Mersenne fold, rotation kernel, 31-point kernel, bit-reversal permutation | `verus/m31_fft.rs` §1–§6 | no Rust/Verus toolchain in this environment |
| I2 | Verus contracts for the quasi-canonical branch-free kernels (`qc_add`, `qc_sub`, `qc_neg`, `qc_mul`, `qc_canon`, mask variants) | `verus/m31_fft.rs` §7 | idem |
| I3 | Verus contract for a lazily reduced additive stage | `verus/m31_fft.rs` §8 | idem |
| I4 | Verus contracts for the circle-FFT butterflies and PFA index maps | `verus/m31_fft.rs` §9–§10 | idem |

For each of I1–I4 the *mathematics* is in category P; what is unverified is the
transliteration into Verus syntax and the SMT-level proof obligations (loop invariants,
`wrapping_*` bit reasoning, aliasing).

## 3. Assumed (A)

| # | Assumption | Comment |
| --- | --- | --- |
| A1 | Rust `u32`/`u64` wrapping arithmetic has the same semantics as Lean's `UInt32`/`UInt64` (`Fin 2³²`, `Fin 2⁶⁴` with wraparound), and `&`, `>>`, `<<` agree | This is the load-bearing modelling assumption of the whole bridge. It is *not* proved here; discharging it means re-proving the `MachineM31` lemmas inside Verus, or trusting a documented correspondence. |
| A2 | The Lean `Expr`/SLP operation counts correspond to machine instruction counts | They do not, literally: the models count field operations (and rotations), not CPU instructions, cache traffic or SIMD lanes. Every cost theorem must be read inside its model. |
| A3 | Cost counts in `OpCount.lean` are per output expression tree | No sharing of common subexpressions between outputs is modelled there. The register model of `SLPLowerBound.lean` does model sharing, but is used only for the length-2 lower bound. |
| A3b | The split-radix and radix-2 counts `S`, `R` are hand-derived from the decomposition identities and the free-twiddle lemmas | They are definitions in the stated model, not counts extracted from a program object; the comparison theorem is a statement about those definitions. |
| A4 | Twiddle tables are precomputed | The cost theorems count the transform proper; generating `1/(2t)` constants is not counted. |
| A5 | **Non-degeneracy of the discriminant of the formal line.**  Every statement of the Path 2 chain (`DiscriminantMCA.lean`, `ThresholdDiscriminant.lean`, `JohnsonDiscriminant.lean`) assumes that for the interpolant `Q` of a line there is an evaluation point `x₀` with `discLine bY x₀ Q ≠ 0` | **REFUTED** (see O32 and `RESULTS.md` §32). The assumption is not merely unproved: it is *false* for the whole parameter schedule of the route, and the theorems carrying it are therefore vacuous.  For a line that lies inside the code (already for `f₀ = f₁ = 0`) the multiplicity conditions force `∏_{x∈D}(X−x)^{m−j}` to divide the `j`-th `Y`-coefficient of every interpolant, while the weighted-degree budget allows degree `< L − kj`; hence `c_j = 0` whenever `(m−j)·n + k·j ≥ L`.  Both `L ≤ m·n` and `L ≤ (m−1)·n + k` hold throughout the schedule, so `Y² ∣ Q` and the discriminant vanishes identically at *every* evaluation point (`Root.CodingTheory.discLine_eq_zero_of_zeroLine`, `nondegeneracy_hypothesis_false`, `johnson_nondegeneracy_false`, `nondegeneracy_false_rho_half/quarter/eighth/sixteenth`).  The statements of the route are left in place, unchanged, with this entry recording that their hypothesis cannot be met. |

## 4. Open / not formalised (O)

Each item carries a decision criterion: what would count as settling it.

| # | Question | Decision criterion | Status |
| --- | --- | --- | --- |
| O1 | Is there an `Ω(n log n)` lower bound for general arithmetic circuits computing the DFT? | A Lean proof of such a bound, or of a bound in an explicitly restricted model (e.g. linear circuits with bounded coefficients over `ℂ`) | **Open in the literature**; nothing here bears on it. No claim is made. |
| O2 | Winograd's `2n − t(n)` for cyclic convolutions of length `n = 3, 4, 5, 6` | A Lean lower-bound proof in the model of `SLPLowerBound.lean` for each length | proved only for `n = 2` (P21) in the straight-line model; for `n = 3` only `2 ≤ ·` there (P24), upper bound 3 over `M31`. In the *bilinear* model the value is settled for every `n` with a primitive `n`-th root of unity: exactly `n` (P25b) |
| O3 | Radix-4 / radix-8 with a proved multiplication count below radix-2 | A cost theorem in one fixed model comparing the two counts | **radix 4 is closed** (P55): in the cost model of `SplitRadix.lean` the free twiddles of all four branches are classified (`radix4_free_odd_branch`, `radix4_free_even_branch`), giving `3m − 4` per level against `4m − 4` for the two radix-2 levels it replaces, hence `radix4Cost_lt_radix2Cost` for every `k ≥ 4` and `splitRadixCost_le_radix4Cost`.  Radix 8 is now also formalised (P57), with the honest verdict that in this unit-cost model it does **not** improve on radix 4: `radix8Cost_le_radix2Cost` and `radix4Cost_le_radix8Cost`, so `S ≤ R₄ ≤ R₈ ≤ R₂`.  The model charges one unit for every non-`μ₄` constant and so cannot see the cheapness of the eighth roots, which is what a real radix-8 kernel exploits |
| O4 | Bluestein / truncated FFT for arbitrary `n` | correctness + cost theorems | **Bluestein is formalised on the correctness side** (P56): `dft_eq_chirp_conv` reduces the length-`n` DFT to one cyclic convolution of any length `L ≥ 2n − 1` with no hypothesis on `n`, `dft_eq_chirp_conv_odd` supplies the chirp from `⟨ζ⟩` itself at odd `n`, and `M31.dft31_eq_chirp_conv63` is the length-31/length-63 instance over `M31` with all chirp constants powers of two.  No operation-count theorem for Bluestein is stated, and the truncated FFT is still not formalised |
| O5 | Short Winograd convolutions of length 5 and the tensor product realising the length-30 Rader convolution | explicit programs + correctness + multiplication counts | in the *straight-line* model lengths 2 (P21) and 3 (P24) are done and length 5 is not. In the *bilinear* model the tensor construction is now proved (P25f) and gives 54 products for length 30 over `M31`, with a 9-product length-5 factor coming from Toom–Cook; a shorter length-5 algorithm (8 products via `x⁵−1 = (x−1)Φ₅`) is not formalised, so the exact value for length 30 (between 30 and 54) is still open. **Resolved on the upper-bound side** (P28): the 8-product length-5 algorithm is now formalised and kernel-checked, and the `6 ⊗ 5` tensor gives 48 products for length 30 — exactly the Winograd target `2n − t(n) = 48` (P26). What remains open is only the *lower* bound: the Alder–Strassen/Winograd theorem `R(A) ≥ 2 dim A − t(A)` for commutative algebras is not formalised (the field-extension case `t = 1` is, as P27), so the proved range was `30 ≤ c ≤ 48`. **Closed** (P29–P32): the Alder–Strassen/Winograd lower bound is now formalised, so the length-30 value is exactly 48, and more generally `c(n) = 2n − t(n)` for every admissible `n` |
| O6 | Radix-2 NTT over `𝔽_{p²}` and a cost comparison against the circle approach | a proved inequality between the two counts in one model | **closed** (P58): `extRadix2_correct` gives the extension NTT (primitive `2^k`-th root for `k ≤ 32`, radix-2 recursion correct), and in base-field multiplications `extBaseMuls = 3 · circleBaseMuls` — the same butterfly count, but an `𝔽_{p²}` multiplication costs exactly three base multiplications (`M31sq_bilinear_complexity`).  Hence `circle_lt_ext_baseMuls` for every `k ≥ 1`, and `circle_lt_ext_packed` keeps the circle route ahead by `3/2` even against the two-transforms-in-one packing trick.  Only multiplications are counted; no benchmark |
| O6b | Winograd's exact value 3 for the multiplicative complexity of multiplication in a quadratic field extension (optimality of Karatsuba) | a Lean lower-bound proof of `3 ≤ mulCount`, which needs the "at most two general multiplications" normal form | only `2 ≤ · ≤ 3` proved (P21b) in the straight-line model. The analogous question for plain polynomial multiplication *is* settled in the bilinear model (P25c) |

| O8 | Iterative in-place FFT with loop invariants and disjointness of accesses | a Lean-level (or Verus-level) proof about the imperative loop | **Closed on the Lean side** (P34): the pass loop invariant, the permutation-loop invariant, correctness of the composite algorithm, the fixed-point-free involution/locality facts that justify in-place updates, the index-range bound and the operation counts are all proved in `InPlaceFFT.lean`; arrays are modelled as functions `ℕ → F`, so what remains is the Rust-memory-level replay in Verus (section 11 of `verus/m31_fft.rs`), still unchecked here for lack of a toolchain |
| O9 | Isotypic decomposition of `Rep_F(C_n)` as a natural isomorphism of functors | a Lean `NatIso` | **closed** (P59), `RequestProject/IsotypicNatIso.lean`: the diagonalisation functor `FFT.diagFunctor ζ n : Rep K C_n ⥤ ModuleCat K` and the natural isomorphism `FFT.diagNatIso : diagFunctor ζ n ≅ Action.forget (ModuleCat K) C_n`, with the two computation rules identifying it with the DFT (`diagNatIso_hom_apply` sums the isotypic components, `diagNatIso_inv_app` takes the Fourier modes `(1/n) ∑_k ζ^{−jk} ρ(g)^k v`), plus the `M31` instance `FFT.M31.diagNatIso31` at `n = 31`, `ζ = 2`.  The earlier partial answers (P25e, P25g) are unchanged |
| O10 | Determinant of the DFT matrix over `𝔽_p` in terms of Gauss sums / quadratic residues | a closed formula proved in Lean | not formalised (only `det W(ζ)²`, P6) |
| O11 | Operads/associahedra, spectral sequences, Čech cohomology of index coverings | a decidable formulation first | not formalised; abandoned unless a decidable statement is written down |
| O12 | Which circle-FFT twiddles lie in `⟨2⟩` (hence are free rotations) | a Lean characterisation of `{i : circleTw q m k i ∈ ⟨2⟩}` | **closed** (P60), `RequestProject/CircleFreeTwiddles.lean`.  The Chebyshev doubling map `π(x) = 2x² − 1` gives `p^{2^k} = 1 ↔ π^k(p.x) = 1` (`FFT.Circle.pow_two_pow_eq_one_iff`), so the question becomes a finite base-field iteration.  Result: for every circle FFT with `m + 2 ≤ 27`, at every level and index, a twiddle lying in `⟨2⟩` equals `1` or `2¹⁵ = 1/√2` (`FFT.Circle.MersenneFree.circleTw_free`); both bounds are sharp (`pt45_order`: the order-8 point `(2¹⁵, 2¹⁵)`; `pt27_order`: a third value at order `2²⁸`).  The complete table up to the whole circle group `2³¹` is `chebD_two_pow_iff` / `freeLevel_card`: `1, 2, 3, 5, 8, 16` free values at `m ≤ 2`, `3 ≤ m ≤ 27`, `28`, `29`, `30`, `31`.  The earlier numerical expectation of a negative answer is confirmed, and made exact |
| O13 | Partition-rank lower bound on multiplicative complexity (`R_{d−2,1,1}(f) / ((d+1)2^d(d−1)) ≤ L(f)` for `d`-tensors, `d ≥ 3`) | a Lean definition of the partition rank of a `d`-linear form plus a proof of the inequality in the project's straight-line model | **not formalised, and not verified here**: Mathlib has no partition rank, and the statement was not checked against a source in this environment. The `d = 3` shadow of it — a lower bound on the number of general multiplications by a rank-type invariant — is what the bilinear-model results P25b, P27, P29–P32 provide. Nothing in this repository asserts the general inequality |

| O14 | T2 — the FRI-style proximity gap for the affine line test (`δ_d(f) ≤ 1 − α(f) + c·d/q`) | the missing low-degree-test lemma (consistency of the local polynomials on a dense set of points, via the two-dimensional surface argument) | **not formalised**.  What is proved on this route is the algebraic layer: restriction of a degree-`< d` polynomial to an affine line stays of degree `< d`, and the line test is complete (`Root.CodingTheory.reedSolomon_restrict_line`).  The soundness direction is open here |
| O16 | The list-decoding rows of the MCA table (`ε_mca` at the Johnson radius `δ < 1 − √ρ`) | a Lean proof bounding the number of bad points of a line beyond the unique-decoding radius | **partially formalised**.  Proved: the row `#bad ≤ n·Λ` with `Λ` a list-decoding quantity, valid for `2e + √(n(k−1)) < n`, i.e. `δ < (1 − √ρ)/2` — *half* the Johnson radius (`Root.CodingTheory.card_badSet_le_listSizeMax`, `epsMCAmax_le_listSizeMax`, explicit form `epsMCAmax_le_johnson`).  The full Johnson radius `δ < 1 − √ρ` is still open; the proof sketch supplied with the request does not close in this form and was not used   **Update**: the full Johnson radius is now reached on the discriminant route (§31), under assumption A5; unconditionally, the best radius proved here is `1 − (ρ(1+1/m))^{1/4}` (`epsMCAmax_le_pairCover_gs`, §30) |
| O17 | The asymptotic threshold `δ* = 1 − √ρ` for Reed–Solomon proximity/correlated agreement | a Lean statement and proof (or refutation) of the threshold behaviour | **not formalised**.  What is proved is the half-threshold `δ < (1 − √ρ)/2` (§27.10–27.11 of `RESULTS.md`).  The two-point argument used there cannot reach `1 − √ρ`: two witnesses of agreement `n − e` overlap only in `n − 2e` positions, which is vacuous once `2e > n`.  No statement in this repository asserts the full threshold |
| O18 | Theorem CA in the requested form: `Λ(C,e) < |G(f₀,f₁,e)|` implies correlated agreement with `|S| ≥ n − e` | a Lean proof of that exact threshold | **not formalised**.  Proved instead: `2e·Λ(C,2e) + 1 < |G|` implies correlated agreement (`Root.CodingTheory.correlatedAgreement_of_card_goodZ_gt`), unconditionally in `k, e, n, |F|`.  The polynomial loss (`2e`, and the list radius `2e` instead of `e`) is harmless for the MCA bound `ε_mca ≤ n·Λ/|F|`, which is obtained in that form |
| O15 | T3 — an explicit counterexample refuting a stronger proximity statement | a concrete `f` over a small field with `α(f)` large and `δ_d(f) ≥ τ₀`, checked by `decide` | **not formalised as a numeric example**.  The general obstruction is proved instead: `Root.CodingTheory.le_acceptProb_of_agreement` shows that a word agreeing with a codeword on `a` positions is accepted with probability at least `C(a,s)/C(n,s)`, so no threshold below that value can be claimed |
| O19 | Reuse of the external Lean 4 formalisation `z-tech/sumcheck-lean4` (module `LinearCodes`, BCGM25 capstones 6.1/6.2/9.2) as a base for the MCA statements | a bridge file relating their definitions to ours, building in this project | **not possible here, and inspected rather than assumed**.  The repository was cloned and read.  Its `lean-toolchain` pins a Lean release later than the one this project is built with, so its modules cannot be imported into this build at all.  Independently of that, its bad-event bound is proved under a hypothesis of the shape `γ·(ℓ+1) < δ_C/n`, i.e. a unique-decoding-type regime comparable with what this project already had; the Johnson radius enters only through the list-size hypothesis.  So no bridge was written and nothing was imported: §28 is self-contained |
| O20 | The **full** Johnson-radius MCA bound `ε_mca(C,e) ≤ C(ρ,η)·n²/|F|` for `e ≈ n(1 − √ρ − η)` (Haböck 2025 Thm 2 / BCGM25 Thm 9.2) | a Lean proof of correlated agreement at radius `δ < 1 − √ρ` | **not formalised**.  Proved instead are two incomparable regimes: `δ < (1 − √ρ)/2` with a bounded list-size constant (`epsMCAmax_le_gs`, `epsMCAmax_le_gs_relative`) and `δ < (1 − ρ)/3` with error `(2e+1)/|F|` (`epsMCAmax_le_third`).  The missing ingredient is the trivariate interpolation `Q(X,Y,Z)` over the formal line together with the discriminant/Hensel-lifting step of BCIKS20 §5; the bivariate half of that machinery (weighted degree, multiplicities, interpolation, factorisation, list size at the full Johnson radius) *is* formalised in §28.1–28.2   **Update (Path 2)**: the missing ingredient — trivariate interpolation on the formal line plus the discriminant step — is now carried out (`RESULTS.md` §31), so the bound `ε_mca ≤ C(ρ,η)·n²/|F|` at radius `1 − √ρ − η` is proved as `epsMCAmax_le_johnson_disc`, **but under the non-degeneracy assumption A5**; the unconditional status of this row is therefore unchanged |
| O21 | The threshold identity `sup {δ : ε_mca(C,δn) ≤ 2⁻¹²⁸} = 1 − √ρ` (Step 6.3 of the work package) | a Lean statement and proof of the supremum, or of both inequalities | **not formalised**.  Only the lower bound `sup ≥ max((1 − ρ)/3, (1 − √ρ)/2)` follows from what is proved (`exists_const_epsMCAmax_le`, `epsMCAmax_le_third`).  The matching upper bound would need a family of lines with many bad points just above the Johnson radius, which is not constructed here.  Nothing in this repository asserts the identity   **Update**: with A5 assumed, the lower bound improves to `sup ≥ 1 − √ρ` (`epsMCAmax_le_johnson_disc`); the matching upper bound is still not constructed, so the identity remains unproved |
| O22 | The requested concrete instance `threshold_rho_half` with the hypothesis `2⁶⁴ ≤ |F|` | either a proof, or the exact field size for which it holds | **the requested hypothesis is unsatisfiable and was corrected**.  Every bound proved here (and every bound of the form `ε_mca = Θ(n/|F|)` or `Θ(n²/|F|)` in the cited literature) is at least `1/|F|`, so with `n = 2²⁰` a field of size `2⁶⁴` cannot give `2⁻¹²⁸`: already `n/|F| = 2⁻⁴⁴`.  The concrete theorems therefore carry the exact field size the constant requires: `|F| ≥ 2¹⁵¹`, `2¹⁵²`, `2¹⁵²`, `2¹⁵³` for `ρ = 1/2, 1/4, 1/8, 1/16` in `MCAJohnsonGS.lean`, and `|F| ≥ 2¹⁴⁷`, `2¹⁴⁸` for `ρ = 1/2, 1/4` in `CorrelatedAgreementRefined.lean` |
| O23 | Okamoto, ePrint 2025/1712, abstract: a *complete resolution of proximity gaps for Reed–Solomon codes*, i.e. unconditional rigidity up to capacity | a Lean proof of the Δ ≥ 2 rigidity theorem (Thm 7.1/7.2) in the stated generality | **the paper's claim is not supported by its own proof, and only the part that is correct was formalised**.  In the paper's notation `d` is the dimension (our `k`), `k` the error budget (our `e`), `m = n − d`, and `Δ = t − d = m − k`.  The Δ ≥ 2 rigidity of §7 is proved only under the algebraic side condition `(r+1)d < m+1`; with the optimal `r = 2` this reads `3e < n − k + 1`, i.e. the unique-decoding regime — far below the Johnson radius, let alone capacity.  Moreover the conclusion `|S′| ≥ (1−δ)n` of Thm 8.1 does not follow from the witness route used there, which only produces a set of size `≤ m − 1`.  What is formalised is (i) the geometric core of the lens (`proximity_iff_syndrome`, `Syndrome.syndromeLine_trapped`, `mem_supportSpan_iff_isCloseOn`, `supportSpan_eq_top`), and (ii) a *sharpened* form of Thm 7.2 obtained by rounding the count, giving `#bad ≤ e + 1` in the regime `k + 3e ≤ n` (`card_badSet_le_succ`).  No capacity-regime statement is asserted anywhere in this repository |
| O24 | `mca_reduces_to_ca_below_capacity` — Okamoto §8: below capacity MCA reduces to ordinary CA, with an explicit constant `C_capacity` giving `ε_mca ≤ C_capacity·n²/|F|` | a Lean theorem with that constant | **not formalised, and the surrounding claim is refuted at the capacity radius itself**.  The reduction in §8 relies on Thm 8.1, whose gap is described in O23.  In its place the *capacity barrier* is proved: at `e = n − k` the premise is vacuous (`capacity_premise_vacuous`, every point of every line is `(n−k)`-close) and correlated agreement genuinely fails (`capacity_agreement_sharp`).  So no `C_capacity` of that shape can exist at the capacity radius |
| O25 | Path 2 — resultant/discriminant containment: `badSet_subset_discriminant_roots`, `card_badSet_le_discriminant_degree`, `discriminant_degree_bound` (Haböck ePrint 2025/2110, BCIKS20 §5) | Lean proofs building on the existing GS interpolation | **now formalised, under one explicit assumption (A5)**.  §31 of `RESULTS.md`: interpolation on the formal line (`GS.exists_line_interpolating`), the double-root lemma (`GS.sq_dvd_of_agreement`), the containment `bad ⊆ roots(disc)` (`eval_discLine_eq_zero_of_isBad`), the degree bound `deg_Z disc ≤ (2bY−1)·dZ` (`natDegree_discLine_le`), the bad-set bound (`card_badSet_le_disc`), the `ε_mca` bounds (`epsMCAmax_le_disc`, `epsMCAmax_le_disc_clean`, `epsMCAmax_le_johnson_disc`) and four concrete `2⁻¹²⁸` thresholds at `n = 2²⁰`, `|F| ≥ 2¹⁶⁰`.  What is *assumed* is the non-degeneracy A5.  The reported Haböck bound `|E| ≤ ℓ⁷/(3(ρn)²)` was still not used: the constant obtained here is different (see O29) and was derived from scratch |
| O26 | Path 3 — interleaved Reed–Solomon stability, `ε_G(C^{≡s}, δ) ≤ (1 + 1/q + … + 1/q^{s−1})·ε_G(C, δ)` with exact transfer for affine-line MCA (ePrint 2026/891) | a Lean definition of the interleaved code and the transfer theorem | **not formalised**.  This was the lowest-priority path in the instruction and was not reached.  No statement in this repository depends on it |
| O27 | Path 4 — Jo, ePrint 2026/1432: every affine line has at most `O_{r,h}(K⁶)` bad parameters, hence `ε_mca = O_{r,h}(K⁶/q)`, and `ε_mca < 2⁻¹²⁸` for `K = 2¹⁸` at `ρ ∈ {1/2, 1/4, 1/8, 1/16}` | a Lean proof of the `K⁶` bound and of the concrete `2⁻¹²⁸` thresholds | **the circuit-incidence part is formalised in full; the `K⁶` bound is not**.  Theorem 4.2 of that paper (the circuit-incidence bound, `#bad·C(T_eff−1, a−1) ≤ C(n,a)`) together with its Lemma 4.1 (rejecting-test abundance) are proved from scratch here as `card_badSet_le_circuit` and `card_rejectingSets_ge`, with the direction criterion (`not_isCloseOn_snd_of_witness`) supplied by our own `lineCloseOn_of_two_close_on`.  The `K⁶` theorem, however, does **not** come from Theorem 4.2: in the paper it is derived in §3 from an imported external result, which was not formalised.  Taken on its own the circuit bound optimises at `a = K+1` and equals `C(n, K+1)/C(n−E−1, K)`, which grows exponentially in `K`; it is therefore unconditional in the error budget — valid past the Johnson radius and up to the capacity radius — but numerically meaningful only for short codes.  The concrete instance proved here is accordingly at short length: `n = 64`, `k = 16`, `e = 40` (`δ = 0.625 > 1 − √ρ = 0.5`) gives `ε_mca ≤ 2³³/|F|` (`epsMCAmax_le_circuit_64_16_40`).  **No `2⁻¹²⁸` claim at `K = 2¹⁸` is made in this repository** |
| O28 | Non-vacuity of the capacity barrier at realistic parameters | a version of `capacity_agreement_sharp` without a counting hypothesis | **the hypothesis is real and is stated honestly**.  `capacity_agreement_sharp` assumes `C(n, n−k−1) < |F|²`, which is what the pigeonhole construction of the counterexample needs.  It holds for short domains over large fields — a non-vacuous instance over `𝔽₅` with `n = 5`, `k = 2` is proved (`capacity_agreement_sharp_zmod5`) — and fails at FRI scale, where the theorem says nothing.  `exists_no_correlatedAgreement_at_capacity` carries the same hypothesis |
| O29 | The requested Path 2 radius `γ = 1 − (1 + 1/(2m))·√ρ` with the *same* `m` as ordinary Guruswami–Sudan list decoding | a Lean proof of the containment at that radius | **not attainable on this route, and the deviation is stated in the theorems**.  The discriminant argument needs a *double* root, hence two margins: the usual `L ≤ m·t` **and** `L ≤ (m−1)·t + k`.  The second is strictly stronger, and taking `L = (m−1)t + k` the counting condition forces `t ≳ √(kn)·(1 + Θ(1/m))`, i.e. radius `1 − √ρ·(1 + Θ(1/m))`.  The *content* is the same — Johnson radius up to an arbitrary slack `η` — but the multiplicity needed is larger than `⌈√ρ/(2η)⌉`: the rule proved here is `m = max(4, ⌈2√ρ/η⌉ + 1)` (`johnsonM`, `johnson_margin`), and the exact integer search of `analysis/threshold_discriminant_check.py` gives e.g. `m = 866` at `ρ = 1/2`, `η = 2⁻¹⁰`, `n = 2²⁰`.  The necessity of the second margin is not folklore: the control group of `analysis/discriminant_containment_check.py` (only the simple-root condition) produces **43 containment failures out of 107** |
| O30 | The `MvPolynomial (Fin 3) F` model of the trivariate interpolant requested for Path 2 | the same results stated over `MvPolynomial (Fin 3) F` | **modelled differently, deliberately**.  "Trivariate" is the iterated ring `(F[Z])[X][Y] = Polynomial (Polynomial (Polynomial F))`.  This lets the existing bivariate Guruswami–Sudan layer — generalised in this pass to an arbitrary commutative coefficient ring — be reused verbatim with `R = F[Z]`, makes `Z := z` literally `Polynomial.map`, and makes `Res_Y` literally `Polynomial.resultant`.  Nothing is lost mathematically (the two rings are isomorphic), but the statements are not the ones written in the instruction, and a user looking for `MvPolynomial (Fin 3)` will not find it |
| O31 | A bad-set bound on the discriminant route that is *independent of `n`* in the final theorems | the concrete constants for the `n`-free bound | **partly delivered**.  `card_badSet_le_disc` gives `#bad ≤ (2bY − 1)·dZ`, which does not involve `n` at all, and the four concrete thresholds of §31.4 use exactly that (`#bad ≤ 3.3·10⁹`, uniformly in `n` once the counting condition holds).  The *asymptotic* theorem `epsMCAmax_le_johnson_disc`, however, uses the crude closed-form choice `dZ = k·n·m(m+1)(bY+1)` — the one for which the counting condition can be verified symbolically — and therefore states `C·n²/|F|`, the shape asked for.  Deriving an `n`-free asymptotic constant would need the optimal `dZ = ⌈B/A⌉ + 1`, which is not formalised |

| O32 | Removing A5 by perturbation (`exists_t_with_disc_ne_zero`, `exists_nondegenerate_interpolation`, `epsMCAmax_le_johnson_disc_final` and four "final" concrete thresholds) | a Lean proof that some interpolant of every line has a nonzero discriminant | **impossible on this route, and formally refuted**.  The interpolation conditions are linear and homogeneous, so any perturbation `Q₀ ↦ Q₀ + t·M` that preserves them stays inside the same solution space `V(f₀,f₁)`; and for a line inside the code *every* element of `V` is divisible by `Y^{j₀}` with `j₀ ≥ 2` (A5 above), hence has identically vanishing discriminant.  Formalised as `Root.CodingTheory.perturbation_does_not_help` and `Root.CodingTheory.nondegeneracy_hypothesis_false`; pre-verified by brute force over small fields in `analysis/perturbation_check.py` (the structural prediction and the vanishing of the discriminant are confirmed in every degenerate-regime case, and the non-degenerate members reappear exactly when `j₀ = 1`), and audited in exact integer arithmetic for the four concrete parameter sets in `analysis/threshold_discriminant_final_check.py` (`j₀ = 507, 512, 461, 385`).  The requested "final" theorems are therefore **not** stated; the unconditional replacement of the requested shape is `exists_const_epsMCAmax_le_sq` (`ε_mca ≤ C·n²/|F|` for `2δ + √ρ < 1`) |
| O33 | The general polynomial non-vanishing lemma requested for the perturbation step | a Lean proof | **formalised** as `Root.CodingTheory.exists_eval_ne_zero` (a nonzero `P ∈ F[X]` with `deg P < |F|` has a point with `P(x) ≠ 0`).  It is correct and reusable, but it cannot be applied to the discriminant of a perturbed interpolant, because that discriminant is identically zero as a polynomial in the perturbation parameter (O32) |
| O34 | The parity-check matrix of `RS_{<k}(D)` as a **plain Vandermonde** matrix `H i x = x^i` | a Lean definition and a kernel theorem | **the plain Vandermonde matrix is not a parity-check matrix**, and the definition was corrected.  The dual of a Reed–Solomon code is a *generalised* Reed–Solomon code, so the Goppa/GRS multipliers `v_x = (∏_{y ∈ D∖{x}} (x − y))⁻¹` are required: the matrix formalised is `rsParityCheck D k i x = v_x · x^i`, `0 ≤ i < |D| − k`, and `ker_rsSyndromeMatrix` proves its kernel is *exactly* the code.  `analysis/syndrome_trichotomy_check.py` exhibits the failure of the plain matrix over `𝔽₅`, `𝔽₇`, `𝔽₁₁` (it happens to work when `D` is the whole field, which is presumably the source of the folklore statement).  A second deviation: the columns are indexed by the domain `↥D` itself, not by `Fin |D|` — the two differ by a choice of enumeration and `↥D` is the indexing used throughout this development |
| O35 | `mca_reduces_to_ca_below_capacity` with an explicit constant `C_capacity` and hypothesis `e < |D| − k` (Part B3) | a Lean theorem of exactly that shape | **formalised in the strongest form that is actually true, which is not the requested shape**.  `Root.CodingTheory.mca_reduces_to_ca_below_capacity` states: if the probability that a random point of the line is `e`-close exceeds `C(|D|, k+1)/|F|`, then a single agreement set of size `≥ |D| − e` serves the whole line.  This is unconditional in every parameter — in particular the requested hypothesis `e < |D| − k` is **not used**, and is kept only because it was requested (it is marked `_he` and the docstring says so).  A statement of the requested shape `ε_mca ≤ C_capacity·n²/|F|` valid up to `e = |D| − k − 1` is **not** proved and is not claimed: the bound available at that radius is `C(n, k+1)/|F|`, which is not polynomial in `n`, and at `e = |D| − k` itself both sides degenerate (`capacity_premise_vacuous`; checks (i)–(ii) of `analysis/syndrome_trichotomy_check.py`).  See O23, O24 |
| O36 | The Δ = 0 / Δ = 1 / Δ ≥ 2 trichotomy "from Okamoto 2025/1712" as three rigidity theorems | Lean proofs of all three legs | **what is provable is formalised; the Δ ≥ 2 leg is not the paper's capacity-regime statement**.  Formalised: `finrank_supportSpan_eq_card` (dim `U_T = |T|`, i.e. codimension exactly `Δ`, whenever `Δ ≥ 0`), `supportSpan_eq_top_of_margin_zero` (Δ = 0 — the column span is everything, so the premise carries no information), `supportSpan_ne_top_of_margin_pos` (Δ ≥ 1), `finrank_supportSpan_le_of_margin_ge_two` and `card_supportSpan_mul_pow_margin` (Δ ≥ 2 — codimension ≥ 2, i.e. `U_T` has density `|F|^{-Δ} ≤ |F|^{-2}`), and `syndromeLine_eq_of_two_mem` (the trapping mechanism, valid at every margin).  What is *not* formalised is the paper's Δ ≥ 2 rigidity theorem in the generality claimed there, for the reason recorded in O23: its proof needs the side condition `(r+1)k < m+1`, i.e. the unique-decoding regime.  The knife-edge Δ = 1 obstruction already present in this repository is `exists_isBad_knife_edge` (`CircuitIncidence.lean`) |
| O37 | The vanishing-differences theorem with the side condition `(r+1)·k < m+1`, `k` the code dimension | a Lean proof of exactly that statement | **formalised with the corrected side condition, and in a stronger form**.  In the source's notation the error budget is called `k` and the dimension `d`, so the condition is `(r+1)·e < m + 1` with `e` the *error budget* and `m = |D| − k`; transcribed with `k` the dimension it is not the condition the argument needs (with `e = 0` it would make the statement false for large `k`).  Moreover the witness used in `Root.CodingTheory.vanishing_differences_three` is supported on **three** challenges, so the side condition needed is `3e < m + 1` (formalised as `k + 3e ≤ |D|`) *independently of `r`*, which is weaker than `(r+1)e < m+1` for every `r ≥ 2`.  A further strengthening: the three challenges need not be distinct.  The requested `λ`-shaped statement is `Root.CodingTheory.exists_vanishing_combination`.  Pre-verified in `analysis/syndrome_vanishing_check.py`, which also exhibits explicit counterexamples once `k + 3e > |D|` |
| O38 | The global support bound `\|S\| ≤ M·k/(M − (r−1))` under the hypothesis `r − 1 < M` | a Lean proof, and rigidity as a corollary | **the counting bound is formalised as stated (with `e` in place of `k`, and `r = 2`); the rigidity corollary needs a stronger hypothesis than `r − 1 < M`**.  `Root.CodingTheory.global_support_bound` proves `\|S\|·M ≤ M·e + \|S\|`, i.e. `\|S\| ≤ M·e/(M−1)`.  This does *not* round down to `\|S\| ≤ e` at `M = 2`: it gives only `\|S\| ≤ 2e`, the classical two-point bound.  `\|S\| ≤ e` follows exactly when `M ≥ e + 2` (`Root.CodingTheory.card_globalErrorSupport_le`), and that is the hypothesis of the rigidity theorem `Root.CodingTheory.correlatedAgreement_of_many_challenges`.  The threshold is not an artefact: `analysis/syndrome_global_support_check.py` finds that in the sampled instances with `M = e + 1` (over `𝔽₅`, `n = 4, 5`) **every** one has `\|S\| > e` |
| O39 | A `ρ = 1/2` soundness of `2^{-128}` from two independent folds each of per-fold density `1/\|F\|`, with `s = 32` rounds | a Lean theorem with those parameters | **formalised with the honest per-fold density, and with `s = 5`**.  A per-fold density of exactly `1/\|F\|` is not available at `ρ = 1/2`: the proved single-fold bound is `#bad ≤ e + 1`, i.e. density `(e+1)/\|F\|` (`card_badSet_le_succ`, valid in the strict-gap regime `k + 3e ≤ n`), and the `Δ = 1` knife edge (`exists_isBad_knife_edge`) shows the margin cannot be improved to `Δ ≥ 2` for a single fold.  The additive margin law itself is formalised in the requested shape (`Root.CodingTheory.TwoFold.additive_margin_law`, `additive_margin_law_rounds`: `Pr[FA] ≤ (1/\|F\|)^{(Δ₁+Δ₂)·s}`); the concrete theorem `Root.CodingTheory.TwoFold.soundness_rho_half_two_folds` instantiates it at `n = 2²⁰`, `k = 2¹⁹`, `e = 2¹⁶`, `\|F\| ≥ 2³²` with `s = 5` rounds and gives `Pr[FA] ≤ 2^{-128}` (the actual value is `2^{-150}`).  The soundness model is the counting model described in `AdditiveMargin.lean`: a fold is its bad-challenge set, rounds are independent and domain-separated.  Checked numerically in `analysis/syndrome_additive_margin_check.py` |

| O40 | BCHKS25 Thm 1.5 / ABF Thm 4.12 as an **unconditional** theorem: `ε_mca(C, γ) ≤ (A(m,γ,ρ₊)·n + B(m,ρ₊))/\|F\|` at `γ = 1 − √ρ₊ − η` | a Lean proof following the paper (GS interpolation over `𝔽_q(Z)`, `deg Res_Y(Q, ∂_Y Q) = O(m⁵n)`, global factorisation) | **not formalised as in the paper; a different, conditional route reaches a stronger constant**.  What is proved (`BCHKSJohnson.lean`) is the discriminant route of §31 with the sharpened `Z`-degree budget `dZ = ⌊P(bY+1)/A⌋ + 1`: the bad set of a line is then bounded by `2mB(m(m+1)(mB+1)+1)`, a constant **independent of `n`** (`epsMCAmax_le_bchks_disc`), so the requested shape `C(ρ,η)·n/\|F\|` follows a fortiori (`epsMCAmax_le_bchks_linear`).  The price is the non-degeneracy hypothesis (ND′) below.  The paper's own ingredients — the `O(m⁵)` resultant-degree accounting, the factorisation over `𝔽_q(Z)[X,Y]` — are **not** formalised, and no claim is made that the constant proved here is the paper's |
| O41 | Non-degeneracy of the discriminant, after the refutation of (ND) recorded in O32 | either a proof or a refutation of the *restricted* hypothesis | **open, and now stated in the restricted form**.  (ND) is false because of the zero line (O32).  The zero line, and every line spanned by two codewords, has an **empty** bad set (`badSet_eq_empty_of_isCloseOn_univ`) and contributes nothing to `ε_mca` (`epsMCA_eq_zero_of_badSet_empty`), so all counting statements survive with the restricted hypothesis  `(ND′) ∀ f₀ f₁, (badSet k e f₀ f₁).Nonempty → ∀ Q, LineInterpolant … Q → ∃ x₀, discLine bY x₀ Q ≠ 0`,  which is what `epsMCAmax_le_disc_of_bad`, `epsMCAmax_le_disc_clean_of_bad`, `epsMCAmax_le_bchks_*` and the four `threshold_rho_*_bchks` carry.  The refutation of O32 does not apply to (ND′) — it needs an interpolant of a line with a bad point, and the structure theorem only constrains `Q(X, Y, 0)`, i.e. it predicts that `z = 0` is a *root* of the discriminant, not that the discriminant vanishes identically.  Whether (ND′) is satisfiable is **not settled here**, so the four `threshold_rho_*_bchks` and `epsMCAmax_le_bchksRHS_rho_*` statements are conditional and are **not** claimed to be unconditional thresholds |
| O42 | Line-decodability of Reed–Solomon codes at the full Johnson radius, `a = b = O_ρ(n/η⁵)` (ABF §4.4, GG25 Def. 3.1, from BCHKS25 Thm 4.6) | a Lean proof at radius `δ < 1 − √ρ − η` | **the definition and the reduction are formalised; the unconditional radius reached is half the Johnson radius**.  `IsLineDecodable` (`LineDecodable.lean`) is the definition in absolute form, and `isLineDecodable_of_card_badSet_lt` proves `(e, a, a)`-line-decodability — with `b = a`, i.e. **all** proximates collinear — from any bound `#bad < a` together with `k + 2e ≤ n`.  Feeding it the unconditional bounds gives `isLineDecodable_unique_decoding` and `isLineDecodable_half_johnson` (`2δ + √ρ < 1`, `a = O_{ρ,δ}(n)`).  The full Johnson radius is reached only by feeding it the conditional bound of O40/O41 |
| O43 | A lower bound on `ε_mca` matching the *shape* `Ω(n/\|F\|)` of the BCHKS25 right-hand side below the Johnson radius | an explicit family of lines with `Ω(n)` bad points at radius `γ < 1 − √ρ − η` | **open; what is proved is `Ω_ρ(1)/\|F\|`**.  `MCALowerBound.lean` gives the unconditional bounds `ε_mca ≥ 1/\|F\|` (`one_div_card_le_epsMCAmax`, every `k < n` and every radius) and `ε_mca ≥ r/\|F\|` whenever `r·max(n−e, k+1) ≤ n` and `r ≤ \|F\|` (`card_le_epsMCAmax_of_blocks`), i.e. `r ≈ ⌊1/√ρ⌋` in the Johnson regime.  The block construction cannot give more than `⌊n/(n−e)⌋` bad points, and BCHKS25 Cor. 1.7's `Ω(n²/\|F\|)` example lives *at* the Johnson bound in characteristic 2, not below it |
| O44 | The `r ≥ 2` cases of the subspace-design property of folded Reed–Solomon codes, `τ(r) = sρ/(s−r+1)` (GG25 Thm 2.21) | a Lean proof for every `r ≤ s` | **not formalised**.  What is proved is the `r = 1` case, with the sharp constant: `Root.CodingTheory.Folded.foldedRS_design_dim_one` gives `Σ_i dim(H ∩ C_i) ≤ ⌊(k−1)/s⌋` for every line `H = F ∙ c` inside the code.  The `r ≥ 2` cases need the folded-Wronskian argument, which is not in Mathlib and is not developed here.  `analysis/subspace_design_check.py` verifies the GG25 shape exhaustively for `r = 1, 2` on eight small instances (no violation found), so the missing part is the proof, not the statement.  **Partial progress (this round):** `Root.CodingTheory.Alphabet.sum_finrank_inf_coordKer_le` and `Root.CodingTheory.Folded.foldedRS_design_general` prove an *unconditional* design bound for every `r`, `Σ_i dim(W ∩ C_i) ≤ (|W|−1)·⌊(k−1)/s⌋ ≤ (q^r−1)·⌊(k−1)/s⌋`, by a double count (every finite `F`-space has `|V| = q^{dim V} > dim V`, and each nonzero codeword vanishes on at most `⌊(k−1)/s⌋` blocks).  The constant is exponential in `r`, so it does **not** replace the GG25 constant `sρ/(s−r+1)`.  For `r = 2` there is now a sharper, field-size-independent bound: `Root.CodingTheory.Folded.foldedRS_design_dim_two` gives `Σ_x dim(W ∩ C_x) ≤ 4(k−1)` for the plane spanned by two independent folded codewords, via the folded Wronskian `wronsk2_ne_zero` (which needs `γ` of order at least `k`, and that hypothesis is necessary).  The GG25 constant `2(k−1)/(s−1)` for `r = 2`, and the cases `r ≥ 3`, remain open   **Closed (this round).**  `Root.CodingTheory.Folded.foldedWronskian_ne_zero` proves the nonvanishing of the general-`r` folded Wronskian (Casoratian descent), giving `Σ_x dim(W ∩ C_x) ≤ r²(k−1)` (`foldedRS_design_wronskian`), and a multiplicity argument on the shifts `γ^u x`, `0 ≤ u ≤ s−r`, sharpens this to the GG25 constant: `Root.CodingTheory.Folded.foldedRS_design_sharp` gives `(s − r + 1)·Σ_x dim(W ∩ C_x) ≤ r·(k − 1)` for every `r ≤ s`, i.e. `τ(r) = r(k−1)/((s−r+1)|B|) ≤ sρ·r/(s−r+1)`, and `foldedRS_isSubspaceDesign_sharp` states it as the project's `IsSubspaceDesign` predicate.  Hypotheses: `γ ≠ 0` of multiplicative order at least `k` (necessary already at `r = 2`) and `IsFoldingDomain B s γ` (GG25 Def. 2.20). |
| O45 | Curve-decodability of folded Reed–Solomon codes at capacity, `(1, 1−ρ−η, a, b)` with `a = b = O(n/η⁵)` (GG25 Def. 3.1 / Thm 3.4) | a Lean instance of `Root.CodingTheory.Alphabet.CurveDecodable` for `foldedRSCode` at radius `1 − ρ − η` | **not formalised**.  The *implication* `curve-decodable ⇒ MCA` is proved unconditionally over an arbitrary alphabet (`curveDecodable_implies_mca`, `curveDecodable_implies_mcamax`), and the trivial instance `a = |F|` is proved, so the definition is not vacuous; what is missing is the list-decoding input for the folded code.  The only folded MCA bound actually proved here is the unique-decoding-regime one (`card_badSet_folded_le`, radius a third of the block minimum distance) |
| O46 | The BCHKS25 / ABF ordinary-RS Johnson path | an unconditional Johnson-radius MCA bound for ordinary Reed–Solomon | **frozen, and still conditional**.  `epsMCAmax_le_johnson_disc` and the four `2⁻¹²⁸` thresholds `threshold_rho_{half,quarter,eighth,sixteenth}_bchks` remain hypotheses-carrying (refined non-degeneracy ND′, see O32, O40, O41); the discriminant of a single interpolant was shown to vanish identically on lines inside the code (`DiscriminantDegeneracy.lean`), so the hypothesis cannot be removed by perturbation.  No further work was done on this path in the present round, and no unconditional claim is made for it.  The unconditional ordinary-RS radii remain `δ < (1−ρ)/3` and `δ < (1−√ρ)/2` |
| O47 | Route to a capacity-level MCA statement | which development the project pursues as its main route | **the folded (GG25) route is now the main route**, and the alphabet-generic layer for it is in place: `AlphabetMCA.lean` (MCA for an arbitrary finite `F`-module alphabet `A` and an arbitrary `F`-linear code, challenges always drawn from `F`), `AlphabetInstances.lean` (`A = F` reproduces the existing ordinary-RS definitions verbatim), `FoldedRS.lean` / `FoldedMCA.lean` (`A = Fin s → F`), `SubspaceDesign.lean`, `CurveDecodability.lean` (curve-decodability ⇒ MCA, and the additive margin law, both alphabet-generic).  What this route has *proved* so far is unique-decoding-regime, not capacity-level; the capacity-level statement `ε_mca(C, 1−ρ−η) ≤ 2n/(η|F|) + 24/(η³|F|)` (GG25 Thm 1.2) is **not** proved, and depends on O44 and O45 |
| O48 | The Fitting-ideal reformulation of the ordinary-RS interpolation module (bad locus = support of `Fitt₀`) | a Lean development of `Fitt₀` for the Hasse–Schmidt presentation and its degree bound | **not started**.  Recorded here so that it is not mistaken for work in progress |
| O49 | GG25 Theorem 4.7 specialised to lines: *subspace design ⇒ line-decodability at the capacity radius* `1 − τ(r) − ε` with `b = ⌈ε·a⌉`, for `0 < ε ≤ 1/(2r)` | a Lean proof of `SubspaceDesign C τ → LineDecodable C (1 − τ r − ε) a ⌈ε a⌉` | **open**.  The two neighbouring stages are proved: Stage 1 (`LineDecodableGeneric.lean`, line-decodability ⇒ `ε_mca ≤ a/\|F\|`, with the sharp collinearity threshold `b ≥ e + 2`) and Stage 3 (`FoldedRSSubspaceDesign.lean`, the sharp design constant `τ(r) = sρ/(s−r+1)`, row O44).  What is missing is the middle: the pruning/agreement argument of GG25 Thm 4.7 that turns a design into a common line of proximates at radius `1 − τ(r) − ε`.  In its place the project proves a *different*, unconditional bridge (`FoldedRSMCA.lean`): the pair-list route, giving `ε_mca ≤ (e + 2)/\|F\|` whenever `4e` is below the block minimum distance — a unique-decoding-type radius, not the capacity radius.  The purely existential weakening `∃ a b, LineDecodable C (1 − τ r − ε) a b` suggested in the request is **vacuous** (`b = 0`, or `a = 2` with `b = 2` by `two_collinear`) and was deliberately not stated.   *Why the sharp design of O44 does not by itself close this (informal analysis, not a Lean statement):* the natural way to feed a design into the existing pair-list bridge `lineDecodable_of_card_bigAgreePairs` is to pick `t` linearly independent difference-codewords out of the list and intersect their vanishing sets, which costs `4et` coordinates; the resulting condition `4et < (1 − τ(t))n` is monotone in `t`, so it is strongest at `t = 1`, where it is exactly the minimum-distance condition `4e < d` already used.  GG25 Thm 4.7 avoids this loss by using the design as an *average* (random pruning to a common agreement set of density `1 − τ(r) − ε`) rather than by intersecting; that pruning step is the missing ingredient.   **Closed (this round), with the paper-accurate parameters.**  `Root.CodingTheory.Alphabet.subspaceDesign_implies_lineDecodable` (`GG25LineDecodable.lean`) proves `IsSubspaceDesign C τ → LineDecodable C e a ⌈(ε/(r+ε))·a⌉` for every `r > 0`, every `ε ≥ 2/r` and every absolute radius `e ≤ (1 − τ(r) − ε)·n` — i.e. GG25 Thm 4.7 at `ℓ = 1`, with the *lower* bound `ε ≥ (ℓ+1)/r = 2/r` and `b = ⌈(ε/(r+ε))a⌉`, not the earlier (wrong) `0 < ε ≤ 1/(2r)` and `b = ⌈εa⌉`.  The proof is not the paper's; the paper's proof was not available, so a self-contained argument was reconstructed and is the one formalised.  It replaces "random pruning" by a **configuration-space rank count**: attach to each challenge `α` the vector `ψ(α) = (1, α, f α) ∈ F × F × (ι → A)`, let `defectSpace f T` be the vertical part `{w : (0,0,w) ∈ span ψ(T)}` and `defectDim f T` its dimension (`= rank ψ(T) − 2`); then (i) the design applied to `defectSpace f T` gives the *master inequality* `Σ_i defectDim f Tᵢ ≤ τ(r)·defectDim f T·n` over the coordinatewise agreement subfamilies `Tᵢ` (`sum_defectDim_le`); (ii) `defectDim f Z ≤ 2K` with `K = (1−τ(r)−ε)/ε` (`defectDim_le_two_mul_K`, this is where `rε ≥ 2` enters); (iii) strong induction on `|T|` gives `|T| ≤ (1 + K·defectDim f T)·b*(T)` where `b*(T)` is the largest collinear class (`card_le_one_add_K_mul_defectDim`).  Combining, `a ≤ |Z| ≤ (1 + 2K²)·b* ≤ ((r+ε)/ε)·b*`.  Pre-verified exhaustively over small random codes by `analysis/gg25_thm47_line_check.py` (129 proximate families, 0 failures on the theorem and on each of the three pillars). |
| O50 | The capacity-level folded MCA bound `ε_mca(C, 1 − ρ − η) ≤ 2n/(η\|F\|) + 24/(η³\|F\|)` and the derived threshold at `n = 2²⁰`, `η = 2⁻¹⁰`, `s > 2²⁴`, `\|F\| ≥ 26·2¹⁵⁸` | a Lean proof combining Stages 1–3 | **open, and blocked on O49**.  Stage 1 and Stage 3 are proved unconditionally; the combination needs O49.  A concrete `2⁻¹²⁸` threshold *is* proved (`folded_threshold_2_128`, `\|F\| ≥ 26·2¹⁵⁸`, `\|B\| = 2²⁰`) but at the unique-decoding-type radius `4e < \|B\| − ⌊(k−1)/s⌋`, not at `1 − ρ − η`; it must not be read as the GG25 statement.   **Unblocked and closed in shape (this round); the constant is different from the one requested.**  With O49 proved, the chain now composes: `Root.CodingTheory.Folded.foldedRS_isSubspaceDesign_gg25` (the design constant *without* the spurious factor `r`, i.e. `τ(r) = (k−1)/((s−r+1)|B|) = sρ/(s−r+1)`) → `subspaceDesign_implies_lineDecodable` → `Root.CodingTheory.Alphabet.epsMCAmax_le_of_subspaceDesign` → `Root.CodingTheory.Folded.foldedRS_epsMCAmax_le_gg25` / `..._le_capacity`.  The capacity-level statement proved is: for every `η > 0`, with `ε = η/2` and `r = 4/η`, and under the design-slack budget `ρ(r−1) ≤ (η/2)(s−r+1)` (which forces `s = Θ(ρ/η²)`), every radius `e ≤ (1 − ρ − η)·n` satisfies `ε_mca(C, e) ≤ (8/η² + 1)·(e+2)/|F|`.  **The constant is `≈ 8n/η²`, not the requested `2n/η + 24/η³`.**  This is not a slack in the algebra: the bridge `line-decodability ⇒ MCA` needs `b ≥ e + 2`, so `a ≥ ((r+ε)/ε)(e+2)`, and `(r+ε)/ε ≥ 2/ε² ≥ 2/η²` for any admissible pair `(r, ε)` with `rε ≥ 2` and `ε ≤ η`; the coefficient of `n` therefore cannot be brought below `≈ 2/η²` by this route, whatever `r`, `ε`, `s` are chosen.  Consequently the concrete threshold is also different: `Root.CodingTheory.Folded.foldedRS_epsMCAmax_le_two_pow_neg_128` proves `ε_mca ≤ 2⁻¹²⁸` at `n = 2²⁰`, `η = 2⁻¹⁰`, `r = 2¹²`, `a = 2⁴⁴` for `|F| ≥ 2¹⁷²`, **not** for `|F| ≥ 26·2¹⁵⁸ ≈ 2¹⁶².⁷`, which is too small by a factor of about `2⁹`.  All of the composition arithmetic is pre-verified exactly (`fractions.Fraction`, no floating point) in `analysis/folded_rs_thm47_check.py`, which also checks the sharp design constant of `foldedRS_isSubspaceDesign_gg25` on 2.1 million subspaces of small folded codes. |
| O51 | Whether *list-decodability* is an extra hypothesis for `curve-decodability ⇒ MCA` at `ℓ = 1` | a definite answer for the line case | **it is not needed for `ℓ = 1` in the formulation used here**.  `Root.CodingTheory.Alphabet.card_badSet_lt_of_lineDecodable` (`LineDecodableGeneric.lean`) derives `#badSet < a` from `LineDecodable C e a b` and `b ≥ e + 2` alone.  The reason the `ℓ = 1` case avoids a list-decoding input is that the project's bad set is the *strong* one: a challenge is bad as soon as **some** witness set of size `≥ n − e` for its closeness fails to be a common agreement set of the whole line.  A witness set is then produced for each bad challenge, and `b ≥ e + 2` collinear proximates already pin the line down, because two points of an affine line over a field determine it (`two_collinear`) and `e + 2` agreements force the witness set to be a common agreement set.  For `ℓ ≥ 2` (genuine curves) no such statement is claimed here.  The hypothesis `b ≥ e + 2` is sharp: `analysis/line_decodable_implies_mca_check.py` exhibits instances with `LineDecodable C e a (e+1)` and `#badSet ≥ a`. |
| O52 | Whether the project's notion of mutual correlated agreement is *strictly stronger* than GG25 Definition 2.8 (`ℓ = 1`, perfect version) | a Lean comparison of the two definitions | **settled: they are equivalent, not merely related by an implication.**  `RequestProject/Root/CodingTheory/GG25LiteralMCA.lean` states the literal GG25 definition (`GG25MutualCorrelatedAgreement`, with relative radii `δ' ≤ δ` and the failure clause `u₀\|_S ∉ C\|_S` or `u₁\|_S ∉ C\|_S`) and the project's notion packaged the same way (`StrongMCA`, `ε_mca(C, e) ≤ err` at every integral radius `e ≤ δ·n`).  Proved: `strongMCA_implies_GG25MCA` (the implication that was asked for), `gg25MCA_implies_strongMCA`, and hence `strongMCA_iff_GG25MCA` for `n > 0`.  The two bad sets are literally equal radius by radius (`gg25BadSet_eq_badSet`, with `e = ⌊δ'·n⌋`).  The reason is `not_lineAgreeOn_iff`: over a submodule, "some point of the line fails to agree with a codeword on `S`" and "`u₀` or `u₁` fails to agree with a codeword on `S`" are the same condition — one direction is line closure, the other comes from the challenges `γ = 0` and `γ = 1`.  Numerically cross-checked on 1944 instances (small fields, random codes, all radii) by `analysis/gg25_definition_gap_check.py`: 0 mismatches, ratio strong/GG25 always exactly 1. |
| O53 | Whether the literature constant `2n/η + 24/η³` refers to a weaker notion than the one bounded here | a definite answer | **no: both constants bound the same quantity.**  Given O52, the notion bounded by `foldedRS_epsMCAmax_le_capacity` (`≈ 8n/η²`) is exactly the GG25 notion for which `2n/η + 24/η³` is quoted.  The difference is therefore entirely a difference of *proofs*: GG25 obtains its constant from Theorem 4.7 together with the random-pruning argument of §4.2–4.3, whereas the chain here reconstructs a self-contained rank argument (`GG25LineDecodable.lean`) whose bridge to MCA needs `b ≥ e + 2`, forcing `(r+ε)/ε ≥ 2/η²` (row O50).  No definitional trade-off is involved. |
| O54 | The smaller field-size threshold `\|F\| ≥ 2¹⁵⁸`-ish for the concrete instance `n = 2²⁰`, `η = 2⁻¹⁰` | a Lean proof reaching it | **still open.**  What is proved is `\|F\| ≥ 2¹⁷²` (`foldedRS_epsMCAmax_le_two_pow_neg_128`, restated in GG25 language as `foldedRS_gg25MCA_two_pow_neg_128`).  Reaching the smaller threshold requires the GG25 random-pruning proof of Theorem 4.7 with the parameters `b = (ε/(r+ε))·a`, `ε ≥ (ℓ+1)/r`; it is *not* obtainable by weakening the definition, since by O52 there is nothing to weaken.  **Update (this round):** the threshold `2¹⁶²` *is* now proved, but for the slack formulation `SlackCorrelatedAgreement` (common agreement set of size `≥ n − e − 2¹⁰` instead of `≥ n − e`), see row O55 — for the strong notion the threshold is still `2¹⁷²`. |
| O55 | Where the gap to the literature constant `2n/(η\|F\|) + 24/(η³\|F\|)` actually sits | a localisation of the loss, and a proof reaching the literature *scale* | **localised and, for the slack formulation, closed (this round).**  Implementing the GG25 pruning mechanism cannot by itself improve the constant: the conclusion of the pruning argument is exactly GG25 Thm 4.7 for `ℓ = 1`, i.e. `LineDecodable C e a ⌈(ε/(r+ε))a⌉`, which the project already proves (row O49).  The whole loss sits in the *bridge*: the frozen strong bridge (`card_badSet_lt_of_lineDecodable`) needs `b ≥ e + 2`, i.e. `≈ n` collinear proximates, which multiplies the coefficient `(r+ε)/ε ≈ 8/η²` by `n`.  `Root/CodingTheory/SharpLineMCA.lean` adds the sharp bridge: if the common agreement set is only required to have size `≥ n − e − θ` (slack `θ`), then `b ≥ 2` with `e ≤ (b−1)θ` suffices, so `b ≈ 2 + e/θ`.  With `θ = η·n` this gives `a ≈ (8/η²)(2 + 1/η) ≈ 8/η³ + 16/η²`, from which the block length has disappeared, and the concrete instance `n = 2²⁰`, `η = 2⁻¹⁰` needs only `\|F\| ≥ 2¹⁶²` (`foldedRS_slackCA_two_pow_neg_128`), i.e. the same scale as the literature figure `26·2¹⁵⁸ ≈ 2¹⁶²·⁷`.  **Caveat, stated plainly:** the conclusion obtained at that threshold is correlated agreement *with slack* (`SlackCorrelatedAgreement`, common agreement set of size `≥ n − e − θ`), which is weaker than the frozen strong notion (`θ = 0`) of `AlphabetMCA.lean`, for which the proved threshold remains `2¹⁷²` (row O50, untouched). |
| O56 | The probabilistic form of GG25 Lemma C / Thm 4.5 (`Pr[PRUNE_H succeeds] ≥ ε/(r+ε)` for an oblivious distribution `D_H`) | a Lean proof for an explicit distribution | **open, and deliberately not built on.**  Note first that the event is purely combinatorial: the output `S` of `PRUNE_H` always satisfies `H_S = 0` (the recursion stops only at dimension `0`), so the only random event is `S ⊆ Agr`, which depends on the agreement set alone and not on `y` or `c` — this is exactly the obliviousness GG25 exploits.  For the simplest suggested weights `Pr[i] ∝ dim H − dim H_i`, exhaustive exact-rational search over small structured codes (`analysis/gg25_random_pruning_check.py`, Part A: 1052 admissible instances in the regime `ε ≥ 2/r`, `δ = 1 − τ(r) − ε ≥ 0`) found **no violation**, the smallest observed ratio `Pr / (ε/(r+ε))` being `55/14 ≈ 3.9`; but no proof is claimed, and the natural inductive proof (`Pr(H) = Σ_{i ∈ Agr} (dᵢ/W)·Pr(H_i)` with `Pr(H_i) ≥ ε/(dim H_i + ε)`) does **not** close by the design inequality applied to `H` alone: it needs the design property of the *pinned* subspaces as well, and the Cauchy–Schwarz/Jensen relaxations of the required inequality `Σ_{i ∈ Agr} dᵢ²/(m − dᵢ + ε) ≥ Σ_{i ∉ Agr} dᵢ` are false for small `ε`.  What *is* formalised instead is the deterministic core (`exists_pinning_subset`, row P46), which yields the same conclusion for a single word and suffices for every use made of pruning in this project, since the line case (`ℓ = 1`) of Thm 4.7 is already proved by the rank argument of row O49. |
| O57 | An **unconditional** `L = O(1/η)` list-size bound for folded Reed–Solomon *at capacity* (radius `1 − ρ − η/2`) | a Lean proof | **closed as a *finite* unconditional list size (this round); still open at `O(1/η)`, see row O59.**  `foldedRS_capacity_listDecoding_ceil` (§48 of `RESULTS.md`) now proves, with no external input, that folded RS is `L`-list-decodable at every radius `e ≤ (1 − ρ − ε)·n` with `L = ⌈2/ε⌉^⌈2/ε⌉` and `s ≥ 16/ε² + 8/ε + 3`, and `foldedRS_epsMCA_unconditional` turns this into a hypothesis-free capacity-level strong MCA bound.  The `O(1/η)` list size assumed by `foldedRS_epsMCA_literature` and `foldedRS_threshold_2_158` remains unproved, so those two statements are still conditional as written.  Historical status:  This is the only external input of the literature-constant chain of §47 of `RESULTS.md`: `foldedRS_epsMCA_literature` and `foldedRS_threshold_2_158` take `ListDecodable (foldedRSCode B k s γ) (e + ⌊ηn/2⌋) L` with `L ≤ 2/η` as a hypothesis.  It is the capacity-approaching list-decoding theorem for folded RS (Guruswami–Rudra and successors), whose proof needs the linear-algebraic structure of the folded list (an affine subspace of dimension `O(1/η)` cut out by a linearised polynomial) — machinery absent from Mathlib and not built here.  What *is* proved unconditionally in this project are two weaker regimes, and they show the hypothesis set is satisfiable and the mechanism usable: `listDecodable_of_minDist` (`L = 1`, unique decoding, `2e < d`) and `foldedRS_listDecodable_johnson` (Johnson regime, via unfolding to ordinary RS and the formalised Guruswami–Sudan bound `k·(ns)(m+1) < m·T²`, `T = s(n−e)`).  The corresponding unconditional MCA corollaries are `foldedRS_epsMCAmax_amplified_uniqueDecoding` and `foldedRS_epsMCAmax_amplified_johnson`. |
| O58 | The gap between the frozen unconditional `8n/η²` bound (threshold `2¹⁷²`) and the literature constant `2n/η + 24/η³` (threshold `26·2¹⁵⁸`) for the **strong** notion | the GG25 Thm 3.6 amplification mechanism in Lean | **closed modulo O57 (this round).**  Rows O53–O55 had localised the loss in the strong bridge `card_badSet_lt_of_lineDecodable`, which needs `b ≥ e + 2 ≈ n` collinear proximates.  `LineDecodableAmplification.lean` now proves the missing mechanism: `lineDecodable_amplification` turns `(1, e, a, t)`-line-decodability with `t ≥ 2`, `e ≤ (t−1)θ` plus `L`-list-decodability at radius `e + θ` (and `(L+1)² ≤ |F|`) into `(1, e, a + L(b−1), b)`-line-decodability for *every* `b` — an **additive** `L(b−1)` in place of the multiplicative `n`.  Its engine is the pair-collapse lemma `card_bigPairs_le_of_listDecodable` (`ListDecodable.lean`): distinct pairs with a common agreement set give distinct codewords `c₀ + γc₁` for a good challenge `γ`, all close to `u₀ + γu₁`, so there are at most `L` of them.  Composing with the sharp design constant and the pruning count and optimising `ε = η/2`, `r = 4/η`, `θ = ⌊ηn/2⌋`, `t = 2 + ⌈e/θ⌉`, `a = ⌈(8/η²+1)t⌉`, `L ≤ 2/η` yields exactly `ε_mca(C, e) ≤ 2n/(η\|F\|) + 24/(η³\|F\|)` (`foldedRS_epsMCA_literature`) and the threshold `\|F\| ≥ 26·2¹⁵⁸ ⇒ ε_mca ≤ 2⁻¹²⁸` at `n = 2²⁰`, `η = 2⁻¹⁰` (`foldedRS_threshold_2_158`), for the **strong** (`θ = 0`) notion `epsMCAmax`, i.e. exactly the quantity the frozen `2¹⁷²` theorem bounds.  Both carry the list-decodability hypothesis of row O57; nothing frozen was modified, and no axiom was added.  Pre-verified exactly (integers and `fractions.Fraction`) by `analysis/gg25_amplification_check.py`, Parts A–D. |
| O59 | The **optimal** list size `L = O(1/η)` (Chen–Zhang 2025) or `O(1/η²)` (Srivastava 2025) for folded Reed–Solomon at capacity, in place of the `(1/η)^{O(1/η)}` proved in §48 | an induction on folded Wronskian determinants controlling affinely *dependent* families of close codewords | **closed at `O(1/η²)` (this round); still open at `O(1/η)`.**  `SrivastavaInduction.lean` / `SrivastavaAbstract.lean` replace the coset recursion by an *amortised two-budget induction*: the rank deficits are spent against the single global design budget, the terms counting the information-free coordinates cancel identically, and the outcome is `M ≤ 1 + d·r` inside a `d`-dimensional coset at relative radius `δ ≤ (r/(r+1))(1 − τ(r))`, hence `L = 1 + r² = O(1/ε²)` (`foldedRS_listDecoding_quadratic_ceil`, `L = 1 + ⌈2/ε⌉²`, same folding hypothesis `s ≥ 16/ε² + 8/ε + 3`).  The field-size cost at `n = 2²⁰`, `η = 2⁻¹⁰`, `ε_mca ≤ 2⁻¹²⁸` drops from `2^98305` to `2^173` (`foldedRS_epsMCA_unconditional_quadratic`; `analysis/srivastava_threshold_check.py`).  The Chen–Zhang `O(1/η)` list size remains unproved here.  Historical status: **open.**  The sharp design gives the average-radius relaxed generalized Singleton bound only for *affinely independent* tuples (`singleton_bound`), where it is tight; that bounds the affine *dimension* of a list by `d₀ = O(1/η)` but not its cardinality.  Passing from dimension to cardinality is done here by the coset recursion `card_le_of_coset`, which costs a factor `G = O(1/η)` per dimension, hence `L = G^{d₀}`.  Any attempt to absorb the loss by weakening the radius fails: a constant factor in front of `τ ≈ ρ` is fatal at capacity, so only the folding parameter `s` (already `Θ(1/η²)`) can absorb slack.  Concretely this costs `\|F\| ≥ 2⁹⁸³⁰⁵` instead of `26·2¹⁵⁸` at `n = 2²⁰`, `η = 2⁻¹⁰`, `ε_mca ≤ 2⁻¹²⁸` (`analysis/foldedRS_unconditional_threshold.py`, exact arithmetic). |

## 5. Reproducing the Lean verification

```bash
cd <repo>
lake exe cache get      # optional, fetches Mathlib build artifacts
lake build              # builds every module; must end with "Build completed successfully"
rg -n "sorry|admit" RequestProject/          # must print nothing
```

`RequestProject/Main.lean` additionally prints `#print axioms` for the headline theorems;
only `propext`, `Classical.choice` and `Quot.sound` may appear.

The test vectors of `RequestProject/Reference.lean` are theorems proved by `decide
+kernel`, so they are re-checked by the kernel on every build; there is no separate test
command to run.

## 6. Verifying the Verus side (user-side, not done here)

```bash
# install Verus (https://github.com/verus-lang/verus) and its Rust toolchain
verus verus/m31_fft.rs
```

Expect proof obligations to remain: the file is a *contract skeleton*. In particular the
bit-level obligations (`wrapping_add`/`wrapping_sub`/`&`/`>>` reasoning) correspond one to
one with the Lean lemmas listed in the comments of each section; the intended porting
route is to prove them with `bit_vector` / `nonlinear_arith` assertions mirroring the Lean
proofs. No `assume()`/`admit()` placeholders are used anywhere in the file, so a
successful `verus` run would be meaningful.

## 7. Benchmark protocol (user-side, not done here)

No timing measurement was performed. A meaningful comparison would need, at minimum:

1. a fixed reference implementation (name, version, commit) and a fixed problem size
   (e.g. circle FFT of `2²⁰` points over M31);
2. the same machine, pinned CPU frequency, warm caches, ≥ 30 repetitions, median and
   inter-quartile range reported;
3. identical input/output layouts (bit-reversed vs natural order must be stated);
4. a separate report of the operation counts predicted by the Lean cost theorems, so that
   model and measurement can be compared rather than conflated.

Until such a protocol is run, all statements in this repository about "cost" refer to the
formal operation-count models only.

---

## 8. Addendum — linear list size for folded RS (§50 of `RESULTS.md`)

### 8.1 Proved in Lean (P)

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P50a | The double count `\|S\|(n−e) ≤ n + excess`, and the bridge: `excess ≤ (\|S\|−1)T` together with `e ≤ (L/(L+1))(n−T)` gives `\|S\| ≤ L+1` | `card_le_succ_of_excess_le` | `ExcessAmortisation.lean` |
| P50b | Universal pointwise bound `excess ≤ (\|S\|−1)·∑_i dim(V ⊓ Ker_i)` in a coset of `V` | `excess_le_card_sub_one_mul_sum_finrank` | `ExcessAmortisation.lean` |
| P50c | Excess budget unconditionally on a line; linear list size `L+1` there | `excess_le_of_finrank_le_one`, `line_list_bound_linear` | `ExcessAmortisation.lean` |
| P50d | Excess budget unconditionally on a **plane**, with constant exactly 1; linear list size `L+1` there | `excess_le_of_finrank_le_two`, `plane_list_bound_linear` | `ExcessAmortisation.lean` |
| P50e | An excess budget `T ≤ ρn` for folded RS gives list size `2^11` and `ε_mca ≤ 2^-128` at `\|F\| ≥ 26·2^158` | `foldedRS_listDecodable_linear_of_excessBudget`, `foldedRS_threshold_linear_2_158_of_excessBudget` | `FoldedRSLinearMCA.lean` |
| P50f | Sharpness: the `F₃` repetition code is a `τ ≡ 0` subspace design that is **not** `(2,2)`-list-decodable but is `(2,3)`-list-decodable | `repetitionThree_not_listDecodable_two`, `repetitionThree_listDecodable_three` | `LinearListSharpness.lean` |

All of these carry only `propext`, `Classical.choice`, `Quot.sound` (audited by the
`#print axioms` block at the end of `RequestProject/Main.lean`).

### 8.2 Discrepancy with the mission statement

| # | Requested | What is true | Evidence |
| --- | --- | --- | --- |
| D50.1 | "for every affine layer `H` of dim `d ≤ r`, if `δ ≤ (r/(r+1))(1−τ(r))` then `\|list ∩ H\| ≤ C₁r + C₂`" read with the implicit `C₁r + C₂ = r` | **False** for `C₁r+C₂ = r`. The correct sharp shape is `L + 1`, i.e. `C₁ = C₂ = 1` | `repetitionThree_not_listDecodable_two` (formal), plus 714 counterexamples to the naive form found by exact-arithmetic search |
| D50.2 | Linear list size for *all* layer dimensions | Proved unconditionally only for `d ≤ 2`. For general `d` the linear bound is proved **conditionally** on `HasExcessBudget`, an explicit hypothesis of every theorem that uses it (never an axiom) | `ExcessAmortisation.lean`, `FoldedRSLinearMCA.lean` |
| D50.3 | "threshold `\|F\| ≤ 2^160`" as a success criterion | The `26·2^158` threshold is a theorem **with the excess-budget hypothesis**. The repository's *unconditional* threshold is unchanged at `2^173` (§49), which is retained as required by the freeze list | `foldedRS_threshold_linear_2_158_of_excessBudget` vs. `foldedRS_threshold_quadratic_2_173` |

### 8.3 Open (O)

| # | Question | Decision criterion | Status |
| --- | --- | --- | --- |
| O50.1 | The excess budget `(EXC)`: `∑_i (occ(K_i) − 1) ≤ (M−1)·T` with `T = max_{0≠U} (∑_i dim(U ⊓ K_i))/dim U`, for layers of dimension `≥ 3` | a Lean proof, or an explicit counterexample | **Open.** No counterexample in exact-arithmetic search: 0 violations over 88 brute-forced small linear codes, 300 abstract configurations and 540 excess configurations. Dimensions 1 and 2 are proved (P50c, P50d) |
| O50.2 | Which strengthening of `(EXC)` could carry an induction on dimension | a Lean proof | Six candidate strengthenings **refuted** numerically: multiplicative/Shearer box theorem (cross in `F_q²`), single-flag `FLAGMIN` (1/540), entropy/Han-dual balancing, point peeling, `∑_i x_i(M − m(K_i)) ≤ (M−1)T` (`F_q²` grid), submodularity of `occ − 1` (two axis lines in `F³`). The coset-splitting recursion is valid but closes only when a *proper* subspace attains `T` |
| O50.3 | Secondary branch: the same amortised root for **ordinary** RS (generalised-RS/syndrome or interpolation-module/Fitting-ideal route) | an abstract instantiation plus a concrete threshold | **Not started** — the mission makes it conditional on the primary goal, which is resolved only in dimension `≤ 2` |

### 8.4 Addendum — the geometric root (§50.7 of `RESULTS.md`)

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P50g | A fractional flag certificate implies the excess budget, hence the linear list size `L+1` | `excess_le_of_flagCertificate`, `hasExcessBudget_of_flagCertificates`, `listDecodable_of_flagCertificates` | `FlagCertificate.lean` |
| P50h | Every affine line and every affine plane carries a certificate; the plane certificate re-proves the dimension-two excess budget without the monotonicity hypothesis `τ(1) ≤ τ(2)` | `flagCertificate_of_finrank_le_one`, `flagCertificate_of_plane_occupancies`, `flagCertificate_of_finrank_le_two`, `excess_le_of_finrank_le_two_certificate` | `FlagCertificate.lean` |

| # | Question | Decision criterion | Status |
| --- | --- | --- | --- |
| O50.4 | Does every finite point set in a vector space carry a fractional flag certificate (equivalently: is the covering LP value always `\|S\| − 1`)? | a Lean proof, or an exact-arithmetic counterexample | **Open in dimension ≥ 3.** Exact simplex over the rationals: 0 counterexamples in 1010 random point sets and in the exhaustive families (all 127 sets of `F₂³` and all 255 of `F₃²` containing `0`, and all 4943 sets of size ≤ 6 in `F₂⁴`); every instance is tight. Two natural greedy constructions of the certificate were refuted on an explicit 8-point example in `F₅³`. Script: `analysis/fractional_flag_lp.py` |

### 8.5 Addendum — the flat-partition mission (§51 of `RESULTS.md`)

| # | Requested | What is true | Evidence |
| --- | --- | --- | --- |
| D51.1 | "Chen–Zhang Lemma 2.18": partition `S` into flats `U_j`; the **characteristic weights** `w_{U_j} = 1` form a flag certificate | **False.** The characteristic weights satisfy the budget but never the covering constraint. For the five points of an affine line in `𝔽₅²` *no* weighting with all weights `≤ 1` covers, while the required coverage is `\|S\| − 1 = 4` and the maximum available is `2` | `flagCertificate_unit_weights_fails` (formal), `sum_finrank_inf_coordKer_one_le_two` (formal); `analysis/flat_partition_check.py`: 801 covering failures, 0 budget failures |
| D51.2 | The invariant `\|S_H\| − 1 + ∑_{rec} dim U_j ≤ \|S\| − 1` as stated (arbitrary hyperplane peeling) | The correct general statement replaces "flats of a partition" by an **independent family of directions**: `∑_j (\|A_j\| − 1) ≤ \|S\| − 1` whenever the `K_j` are independent and `A_j − A_j ⊆ K_j`. Independence is necessary — dependent families violate the bound | `sum_card_sub_one_le_of_indepOn` (formal); `analysis/flag_certificate_general_lp.py` Parts B and C |
| D51.3 | Target A `flagCertificate_of_finrank_le` for all `r` (and hence targets B, C) | **Not proved.** Reduced to the *fractional* independent-flat budget plus LP strong duality; Mathlib provides no Farkas/LP-duality theory. Proved instead: two general-dimension certificate constructions covering the extreme regimes, and the exact obstruction family | `flagCertificate_of_density`, `flagCertificate_of_indep_flats`, `weighted_excess_le_of_flagCertificate` |
| D51.4 | Success criterion "final MCA threshold `≤ 2^160`" | **Unreachable with this constant.** Even a linear list size `L = ⌈2/η⌉ = 2¹¹` gives exactly `\|F\| ≥ 26·2^158 = (13/8)·2^162 > 2^160`. The mission's own "expected `≈ 2^158`" is the mantissa form `26·2^158`, not a power-of-two bound `2^158` | `analysis/chenzhang_linear_threshold_check.py` (exact `Fraction` arithmetic) |

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P51a | Independent-flat budget (the corrected inductive partition lemma), in every dimension | `sum_card_sub_one_le_of_indepOn` | `FlatPartition.lean` |
| P51b | Certificate from a single layer when no coordinate is denser than the layer | `flagCertificate_of_density` | `FlatPartition.lean` |
| P51c | Certificate from an independent family of flats, weights = occupancy excesses | `flagCertificate_of_indep_flats` | `FlatPartition.lean` |
| P51d | Characteristic (unit) weights are not a certificate | `flagCertificate_unit_weights_fails` | `FlatPartition.lean` |
| P51e | Fractional-independence obstruction (the LP dual side of the certificate) | `weighted_excess_le_of_flagCertificate` | `FlatPartition.lean` |

### 8.6 Addendum — the finite-LP-duality mission (§52 of `RESULTS.md`)

| # | Requested | What is true | Evidence |
| --- | --- | --- | --- |
| D52.1 | `finite_farkas` as an unconditional equivalence `(∀ x ≥ 0, A x ≤ b → cᵀx ≤ γ) ↔ ∃ y ≥ 0, Aᵀy ≥ c, bᵀy ≤ γ` | **False as stated.** The equivalence needs the primal system `{x ≥ 0, A x ≤ b}` to be feasible; otherwise the left side is vacuous while the right side can be unsatisfiable (`A = 0`, `b = −1`, `c = 1`, `γ = 0`). The theorem is proved with that hypothesis, and the unconditional form is *refuted* in Lean | `finite_farkas`, `finite_farkas_without_feasibility_false`; `analysis/finite_farkas_check.py` (400 exact instances: 0 duality failures, 10 infeasible-primal gaps) |
| D52.2 | "If Mathlib has a separating hyperplane theorem for cones, use it" | Mathlib's cone separation applies to **closed** cones; the closedness of a finitely generated cone (Minkowski–Weyl) is itself absent, so it cannot be applied to a finite inequality system. The finite theory was therefore built from scratch by Fourier–Motzkin elimination | `Root.LP.exists_solution_or_certificate` |
| D52.3 | `flagCertificate_exists_of_excessBound` for "arbitrary finite candidate sets `S` and arbitrary rank bound `r`" | Proved, relative to a **finite candidate family of subspaces** `Λ` (the primal variables of the LP). Farkas needs finitely many variables; with `Λ` prescribed the statement is an exact characterisation, not merely sufficient | `flagCertificateOn_iff_excessBound`, `flagCertificate_exists_of_excessBound` |
| D52.4 | Success criterion "final MCA threshold `26·2^158`" | Met, **conditionally on the excess bound** (no longer on LP duality, which is now proved). The unconditional threshold of the repository is unchanged at `2^173` | `foldedRS_threshold_linear_2_158_of_excessBound` |

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P52a | Fourier–Motzkin dichotomy for finite linear systems | `Root.LP.exists_solution_or_certificate` | `Root/FiniteFarkas.lean` |
| P52b | Farkas' lemma, feasibility form, arbitrary finite index types | `Root.LP.farkas_feasible_iff` | `Root/FiniteFarkas.lean` |
| P52c | Finite LP duality (with primal feasibility) | `Root.LP.finite_farkas` | `Root/FiniteFarkas.lean` |
| P52d | The unconditional duality statement is false | `Root.LP.finite_farkas_without_feasibility_false` | `Root/FiniteFarkas.lean` |
| P52e | Flag certificates ⟺ excess bound (Farkas dual) | `flagCertificateOn_iff_excessBound` | `Root/CodingTheory/FlagCertificateFarkas.lean` |
| P52f | Certificate existence from an excess bound; uniform version | `flagCertificate_exists_of_excessBound`, `hasFlagCertificates_of_excessBound` | `Root/CodingTheory/FlagCertificateFarkas.lean` |
| P52g | Excess bound ⇒ excess budget ⇒ linear list size ⇒ `26·2^158` threshold | `hasExcessBudget_of_excessBound`, `listDecodable_of_excessBound`, `foldedRS_threshold_linear_2_158_of_excessBound` | `Root/CodingTheory/FarkasRootChain.lean` |

| # | Question | Decision criterion | Status |
| --- | --- | --- | --- |
| O52.1 | Does every finite point set admit a candidate family `Λ` satisfying `ExcessBound`? | a Lean proof, or an exact-arithmetic counterexample | **Open**, and now the *only* open link of the chain: LP duality is proved, so this is a purely combinatorial statement about nonnegative coordinate weightings. No counterexample found (§51.4, §52.3 searches) |

### 8.7 Addendum — the Weighted Excess Bound mission (§53 of `RESULTS.md`)

#### 8.7.1 Proved in Lean (P)

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P53a | Occupancy `occ S W`, its basic bounds, and the fibre/image splitting of occupancy excess | `occ`, `occ_bot`, `occ_mono`, `occ_sub_one_le_fibres_add_image` | `Root/CodingTheory/Occupancy.lean` |
| P53b | **The Weighted Excess Bound**, unconditionally and in every dimension | `weightedExcessBound` | `Root/CodingTheory/WeightedExcessBound.lean` |
| P53c | The excess bound for the family of all subspaces of a layer | `excessBound_layerFamily` | `Root/CodingTheory/FlagCertificateGeneral.lean` |
| P53d | General flag certificate, all ranks | `flagCertificate_of_finrank_le` | `Root/CodingTheory/FlagCertificateGeneral.lean` |
| P53e | Certificate for every candidate set of at most `r+1` codewords | `flagCertificate_of_card_le` | `Root/CodingTheory/FlagCertificateGeneral.lean` |
| P53f | A budget on candidate sets of `L+2` codewords already gives list size `L+1`; it follows from any subspace design | `listDecodable_of_hasExcessBudgetUpTo`, `hasExcessBudgetUpTo_of_design`, `listDecodable_of_subspaceDesign_general` | `Root/CodingTheory/ExcessBudgetBounded.lean` |
| P53g | Folded RS: the excess budget, linear list size `2^11`, and `ε_mca ≤ 2^-128` at `\|F\| ≥ 26·2^158` — **all unconditional** | `foldedRS_excessBudget`, `foldedRS_listDecodable_linear_unconditional`, `foldedRS_threshold_linear_2_158_unconditional` | `Root/CodingTheory/FoldedRSLinearUnconditional.lean` |
| P53h | The proposed flat-partition independence lemma is **false** (explicit `𝔽₃` counterexample, every transversal affinely independent) | `badParts_transversal_affineIndependent`, `flatPartition_directions_not_indepOn` | `Root/CodingTheory/FlatPartitionIndependenceFails.lean` |

All of P53a–P53h are audited in `RequestProject/Main.lean` and depend only on `propext`,
`Classical.choice`, `Quot.sound`.

#### 8.7.2 Discrepancies with the mission statement

| # | Mission statement | What is actually true |
| --- | --- | --- |
| D53.1 | "`flat partition ⟹ IndepOn(K_j)`", supplied as an exact lemma with proof | **False**, formally refuted (P53h). The transversal condition constrains the relative positions of the parts, never their internal directions; two parts may share a direction while every transversal stays affinely independent |
| D53.2 | "Route A is the only accepted route: occupancy weights `(\|T_j\|−1)/dim K_j` + `flagCertificate_of_indep_flats`" | **Cannot work**, for a second and independent reason: `flagCertificate_of_indep_flats` also needs each coordinate explained by one part. For `C = {(a,b,a+b)} ⊆ 𝔽₂³`, `y = (0,0,1)`, every flat partition of `S = C` is three singletons, so all occupancy weights vanish and coverage fails — although a certificate does exist. The bound was proved instead by induction on the layer dimension |
| D53.3 | `flagCertificate_of_finrank_le` with "no additional assumptions" | **False as stated**, already for `r = 0`. The proved statement carries the layer: `V ≤ C`, `dim V ≤ r`, `S` inside a coset of `V` |
| D53.4 | `foldedRS_excessBound` for arbitrary candidate sets | Proved in the bounded form `HasExcessBudgetUpTo … (r+1)`, for the same reason as D53.3. Downstream this costs nothing: the list-size argument inspects only candidate sets of `L+2` codewords |
| D53.5 | Deliverables `FlatPartition.lean` / `exists_flatPartition` / `flagCertificate_of_flatPartition` | Not produced, because D53.1 and D53.2 show the construction they serve cannot yield the certificate. The corrected partition lemma of §51.2 remains in `FlatPartition.lean` and is untouched |

#### 8.7.3 Status changes

* **O50.1** (the excess budget `(EXC)` in dimension `≥ 3`) — **closed**, by P53b + P53d + P53f.
* **O52.1** (does every finite point set admit a family satisfying `ExcessBound`?) —
  **closed affirmatively**: `excessBound_layerFamily` exhibits the family (all subspaces of
  the layer) and proves the bound for it.
* **D50.2** (linear list size for all layer dimensions) — resolved; the general case no
  longer depends on `HasExcessBudget` as a hypothesis.
* **D50.3 / D52.4** (the `26·2^158` threshold) — the threshold is now a theorem with no
  side hypothesis, `foldedRS_threshold_linear_2_158_unconditional`. As required by the
  freeze list, the earlier quadratic `2^173` theorem and the conditional `2^158` theorems
  are retained unchanged.
* **D51.3** (target A for all `r`) — resolved in the corrected form D53.3.

### 8.8 Round 54 — the unified interpolation-module root for ordinary Reed–Solomon

#### 8.8.1 What was delivered

| # | Statement | Lean names | File |
| --- | --- | --- | --- |
| P54a | The generalized interpolation module of the formal line is an `F[Z]`-submodule, and **equals** the weighted-degree submodule intersected with the kernel of the syndrome map | `lineInterpModule`, `mem_lineInterpModule`, `lineInterpModule_eq_inf_ker` | `Root/CodingTheory/GeneralizedInterpolationModule.lean` |
| P54b | Bad-locus containment for the pair resultant, with **no** squarefreeness or non-degeneracy hypothesis, and the degree bound `(bY+bY')·dZ` | `eval_pairRes_eq_zero_of_agreement`, `natDegree_pairRes_le` | same |
| P54c | The counting dichotomy and the resulting MCA bound under the pair non-degeneracy hypothesis | `card_goodZ_le_pairRes`, `card_goodZ_le_or_pairRes_eq_zero`, `epsMCA_le_pairRes`, `epsMCAmax_le_pairRes` | same |
| P54d | Correlated agreement from a formal witness (counting form) and from a witness over `F(Z)` (exact form) | `correlatedAgreement_of_formalWitness`, `correlatedAgreement_of_ratFuncWitness` | same |
| P54e | **Unconditional** proximity gap at every radius with binomial threshold, and the strong MCA corollaries | `correlatedAgreement_of_card_goodZ_gt_choose`, `card_badSet_le_choose_radius`, `epsMCA_le_choose_radius`, `epsMCAmax_le_choose_radius` | `Root/CodingTheory/OrdinaryRSProximity.lean` |

All of P54a–P54e are audited in `RequestProject/Main.lean` and depend only on `propext`,
`Classical.choice`, `Quot.sound`. No `axiom`, no `sorry`, no `admit`.

#### 8.8.2 Discrepancies with the mission statement

| # | Mission statement | What is actually true |
| --- | --- | --- |
| D54.1 | `ordinaryRS_proximity_gap_johnson`: unconditional proximity gap for ordinary RS with the explicit **linear** threshold `((2(m+½)^5 + 3(m+½)δρ₊)/(3ρ₊^{3/2}))·n + (m+½)/ρ₊^{1/2}` | **Not proved.** The interpolation-module route delivers a threshold of exactly this shape — `(bY+bY')·dZ`, linear in `n` at Guruswami–Sudan parameters — but only under the isolated hypothesis that some pair of module elements has a nonvanishing pair resultant (`hnd` of `epsMCAmax_le_pairRes`). What *is* unconditional is the same conclusion at every radius with a binomial threshold `C(n,e)` (P54e) |
| D54.2 | `ordinaryRS_epsMCA_johnson` derived from D54.1 | Derived in both available forms: from the module route under `hnd` (`epsMCAmax_le_pairRes`), and unconditionally with the binomial threshold (`epsMCAmax_le_choose_radius`). The strong MCA definition was **not** changed and was **not** weakened to a slack form |
| D54.3 | `fittingIdealZero` as the ideal of maximal minors of a presentation matrix of `M`, and `fitting_ideal_syndrome_dual` as a separate theorem | Implemented in the equivalent and lighter form `badLocusIdeal` = the ideal generated by the pair resultants of module elements. Mathlib has no multivariate Fitting ideal, and the presentation-matrix minors are not needed: the containment and degree-bound properties that the argument uses are exactly properties of the pair resultants. The syndrome duality is proved at the level of the module itself (`lineInterpModule_eq_inf_ker`), which is stronger than a duality stated only for the ideal |
| D54.4 | "`bad_z_is_zero_of_fitting`: no squarefree hypothesis needed" | **Confirmed and proved** — this is P54b, and it is the reason the pair resultant was chosen over the discriminant of a single interpolant |
| D54.5 | Milestone document for folded RS | Produced: `MILESTONE_FOLDED_RS_CAPACITY.md`, including the `26·2^158` threshold, the list size `2^11`, and the three refuted lemmas |

#### 8.8.3 The precise obstruction

The one missing implication is

> many good `z` ⟹ the interpolation module contains two elements with no common `Y`-factor.

Suppose the two chosen elements do have a common factor `G` of positive `Y`-degree.

* If `G = Y − U` is linear, one still has to show that `U` agrees with the formal line word
  on at least `k` positions before `correlatedAgreement_of_ratFuncWitness` applies; that step
  is a dimension count on the cofactor and is **not** carried out here.
* If `deg_Y G ≥ 2`, the case is genuinely open. A dimension count on the module cannot rule
  it out in the ordinary-RS regime — consistently with the fact that the Johnson radius is
  the natural barrier for this technique — and ruling it out appears to need an effective
  Bertini–Noether statement (an absolutely irreducible bivariate polynomial over `F[Z]`
  specialises to an irreducible one outside a set of `z` of controlled size). Mathlib
  contains no such result, and building it was out of scope for this round.

Two elementary barriers were also identified and are worth recording, because they explain
why no *elementary* argument reaches the Johnson radius with a polynomial threshold:

* two good parameters give correlated agreement only on `2t − n` positions, so pairwise
  arguments stop at half the Johnson radius (this is the barrier the existing
  `CorrelatedAgreement*.lean` results sit at);
* bounding the number of candidate codeword pairs by interleaved list decoding needs
  `2t − n > √(kn)`, i.e. again `δ < (1 − √ρ)/2`.

#### 8.8.4 Status changes

* **New open problem O54.1** — discharge `hnd`: show that for `δ < 1 − √ρ` the interpolation
  module of the formal line always contains two elements whose pair resultant is nonzero, or
  else that the common-factor case always yields correlated agreement. This is the single
  remaining step between the delivered root and an unconditional Johnson-scale proximity gap
  for ordinary Reed–Solomon.
* Capacity for ordinary RS: **not attempted**, per the freeze list.
* The folded-RS results of §53 are untouched.

### 8.9 Round 55/56 — the Fitting-ideal root and the shortening route

**(F) Falsified as stated.**

* *Mission target T2* (`Fitt₀(lineInterpModule f₀ f₁ k m) ≠ 0`).  The interpolation module is a
  non-zero **torsion-free** `F[Z]`-submodule of a free module of strictly larger rank, so the
  0-th Fitting ideal of any generating family is `(0)`.  Formal proof:
  `Root.FittingIdeal.fittingIdealZero_eq_bot_of_torsionFree`; numerical evidence:
  `analysis/fitting_ideal_root_check.py`.
* *Mission target T3* (bad `z` are roots of `Fitt₀`).  In the same experiments the good/bad
  parameters occur at the **generic** specialised rank, so the bad locus is not contained in any
  rank-drop locus of the module.  T3 fails for every Fitting ideal of `M`, independently of T2.
* *Premise of the mission brief* ("Mathlib has `FittingIdeal`").  It does not: Mathlib has only
  the unrelated *Fitting decomposition* of an endomorphism.  The needed theory was written from
  scratch in `RequestProject/Root/FittingIdeal.lean`.

**(C) Corrected form that is true.**  The Fitting ideal that carries the exceptional locus is
that of the **Bézout quotient**, not of the interpolation module:
`Root.FittingIdeal.resultant_mem_fittingIdealZero_bezout` shows the resultant of two polynomials
lies in `Fitt₀(R[X]_{<m+n}/range(Sylvester))`.  So the pair-resultant lemma of §54 is the correct
"Fitting" statement, and it is not replaceable by a module-level non-vanishing lemma.

**(P) Proved for the shortening route.**  Shortening step and converse, bad-parameter transfer,
the double-count `#bad · C(n − e, t) ≤ C(n, t) · B`, the `ε_mca` corollary, the square-root-free
Johnson arithmetic and a concrete `n = 2²⁰` certificate; plus circuit incidence for *generalised*
Reed–Solomon lines, which discharges the sub-Johnson input unconditionally.  All are listed in
§56 of `RESULTS.md` and audited in `RequestProject/Main.lean`.

**(O) Open — the polynomial post-Johnson bound.**  Target "post-Johnson `O(K⁶)`" is **not**
achieved unconditionally.  The reason is precise:

* shortening needs a deterministic bound `B` for generalised lines at the *full* Johnson radius;
* the project's unconditional linear bound (`MCAJohnsonGS.lean`) reaches only **half** the
  Johnson radius, and shortening does not repair this: the shortened instance stays sub-half-
  Johnson only while `2e < (n − t) − √((n − t)(k − t))`, whose supremum over `t ≤ k − 1` is
  `((n − k + 1) − √(n − k + 1))/2`, i.e. essentially the unique-decoding radius — below the
  Johnson radius `n − √(nk)` for every rate;
* the unconditional bound available at every radius (circuit incidence, now also for generalised
  lines) is binomial, not linear.

Consequently `Root.CodingTheory.epsMCA_le_subJohnson` carries `SubJohnsonBound` as an explicit
hypothesis, and the `K = 2¹⁸`, `Q < 2²⁵⁶` prize certificates were not produced.  No axiom, no
`sorry`, and no weakening of the strong-MCA definition was used anywhere.

### 8.10 Round 57 — the degeneracy dichotomy

**Mission claim.** "Either the resultant is nonzero, or the degeneracy itself proves the
theorem", hence the non-degeneracy hypothesis disappears and
`ordinaryRS_badSet_belowJohnson` follows unconditionally.

**What is true (proved).** The dichotomy itself: `resultant_dichotomy` /
`resultant_dichotomy_submodule` in
`RequestProject/Root/CodingTheory/ResultantDichotomy.lean`.  For a line-closed set of
univariate polynomials over a field with a nonzero member, either some pair has nonzero
resultant, or one irreducible polynomial divides every member.

**What is false (refuted, formally).** The second clause — that degeneracy produces a formal
witness giving correlated agreement.  `degenerate_branch_without_correlatedAgreement`
exhibits, for every `k, L, e` with `k + 1 < L ≤ |D|` and `k + e < |D|`, a line whose
interpolation module has two independent elements, has the common factor `Y − U`, and admits
no correlated agreement at the stated budget.  The common factor exists precisely because
the root `U` has `X`-degree exactly `k` — one too large to be a codeword — which is why
`correlatedAgreement_of_ratFuncWitness` (needing degree `< k`) does not apply.  The mission's
"delicate case" (common factor of `Y`-degree `≥ 2` not splitting over `F(Z)`) is therefore
not the obstruction; the obstruction is already present at `Y`-degree 1.

**Second correction.** `pairRes_eq_zero_of_mem_domain`: the specialised pair resultant is
identically zero at every `x₀ ∈ D`.  The non-degeneracy hypothesis of `epsMCAmax_le_pairRes`
can only be satisfied at `x₀ ∉ D`, hence requires `|F| > |D|`.  Earlier rounds did not record
this restriction.

**Consequences for the mission targets.** T1 is delivered.  T2 is **not**: the
`SubJohnsonBound` hypothesis is *not* eliminated, and neither
`ordinaryRS_badSet_belowJohnson` nor the unconditional polynomial post-Johnson theorem is
claimed or present in the project.  The freeze list was respected: no axioms, no `sorry`, no
change to the strong MCA definition, folded-RS and the binomial unconditional post-Johnson
bound untouched.

## 8.11 Round 11 — the Jo chain, and the Chojecki constant radius (D58)

**D58.1 (`SubJohnsonBound` kept, and strengthened in form).**  As instructed, the sub-Johnson
input is *not* derived; it is isolated as `SubJohnsonBoundPoly t C` in `PostJohnsonJo.lean`.
Two deviations from the brief's sketch, both necessary:
(i) the constant is quantified **outside** the field/domain/dimension/line — with the constant
inside, the statement is trivially true (a bad set is a subset of `F`) and the chain would
prove nothing;
(ii) the bound is written `C·(k+1)⁶` in terms of the *shortened* dimension `k = K − t` rather
than `C·K⁶`, so that it is not vacuously strong at `k = 0`; since `t ≥ 1` this implies the
`K⁶` form used downstream.
The older `SubJohnsonBound D k e t B` of `ShorteningMCA.lean` is unchanged and still used as
the interface of `card_badSet_le_subJohnson`.

**D58.2 (an explicit integer gap condition replaces `O_{r,h}(1)`).**  The brief leaves the
shortening depth implicit.  It is pinned here by the integer condition
`4(h+t)²r < t²(r+1)²`, with `exists_shortening_depth` showing `t = 16rh` always satisfies it,
and with the explicit threshold `K > 2t(r+1)(2(h+t)+h²+t)`.  The `K`-threshold is unavoidable:
`analysis/post_johnson_internal_check.py` records that the gain inequality is a genuine
constraint, not decoration.

**D58.3 (the Chojecki structural lemma is false as stated).**  The brief asks to prove

> `∃ t : ℕ, ∀ n ≥ N₀, (n−t)(K−t−1) < (T−t)²`  at a constant relative radius `δ > 1 − √ρ`.

This is false; `not_constant_shortening_for_positive_slack` proves the opposite for every
fixed `t`.  The dimensional reason: at a constant relative radius the Johnson deficit is
`Θ(n²)`, while deleting `t` positions changes both sides by `O(t·n)` only.  The salvaged
statement — with `t = ⌊c·n⌋` for a constant fraction `c` — is proved
(`exists_linear_shortening_for_positive_slack`), under the additional and necessary hypothesis
`ρ < 1 − δ` (for `δ ≥ 1 − ρ` the budget reaches the MDS distance and no bound of any kind can
hold; also `c* < 1 − δ` fails exactly when `ρ ≥ 1 − δ`).

**D58.4 (consequently, no `ordinaryRS_badSet_chojecki_style` theorem).**  The brief's follow-up
instantiation is *not* claimed, and cannot be obtained on this route:
`two_pow_le_choose_div_choose` shows the shortening transfer factor is at least `2^t`, i.e.
`2^{Θ(n)}` at the linear depth that D58.3 forces.  This is recorded as a formal barrier rather
than an open problem: any constant-radius polynomial bound must come from a mechanism other
than agreement-set shortening.

**Freeze list.**  Strong MCA definition unchanged; no slack-MCA; folded-RS capacity results and
the unconditional binomial post-Johnson bound untouched; no capacity-ordinary-RS work; no
axioms; no `sorry`/`admit`.

## 8.12 The BCHKS25 / Jo sub-Johnson package (run of 2026-08-24)

**D59.1 (the claim "no non-degeneracy hypothesis" is not supported by the proposed route).**
The package states that the sub-Johnson bound is proved by "pure Guruswami–Sudan degree
counting + resultant elimination on the formal line", with no Hensel lifting, no Fitting
ideals and no non-degeneracy.  Exact computation
(`analysis/bchks_subjohnson_vs_dichotomy_check.py`) shows that in the multiplicity `m ≥ 2`
regime — the regime in which the double-root lemma applies — every instance that carries a
non-empty bad set has `Res_Y(Q, ∂_Y Q) = 0` *identically*, for every element of the
interpolation module: the repeated `Y`-factor is the correlated-agreement codeword of the
instance.  Resultant elimination therefore degenerates precisely where it is needed.  This is
not a contradiction with the claimed *statement* (no instance violated the bound), but it
refutes the claimed *proof route* at the level of generality asserted.
Formal counterpart: `exists_sqrt_specialisation_of_odd_card` together with `no_formal_sqrt`
shows that a constant fraction of specialisations can acquire a root that comes from no formal
root, so divisibility on the formal line cannot be transported to the specialisations outside a
bounded exceptional set.

**D59.2 (what was removed instead).**  The *specialisation point* of the non-degeneracy
hypothesis is genuinely removable, and is removed: `card_badSet_le_discBiv` needs only that the
interpolant is squarefree in `Y` over `F(Z)(X)` plus `(2bY−1)·dX < |F|`.  The barrier that made
this necessary is now also a theorem: `discLine_eq_zero_of_mem_domain` (multiplicity `≥ 2`
forces the specialised discriminant to vanish at *every* point of the evaluation domain).

**D59.3 (`SubJohnsonBoundPoly` is still a hypothesis).**  Consequently
`PostJohnsonJo.lean` is unchanged: `ordinaryRS_badSet_postJohnson_of_subJohnson` and
`ordinaryRS_epsMCA_postJohnson_of_subJohnson` remain conditional.  The mission's Step 3
("remove SubJohnsonBoundPoly") is **not** carried out, and no unconditional post-Johnson
polynomial bound is claimed anywhere in the project.

**D59.4 (the prize table is only partly reachable).**  With the exact minimal shortening depth
at `K = 2¹⁸`, the chain certifies `2⁻¹²⁸` (conditionally) for the rows `1/4` (first step),
`1/8` (first and second step) and `1/16` (first and second step), with the explicit admissible
constants listed in `RESULTS.md` §59.5.  The row `rate 1/2` of the package's Table 1 is
**refuted for this chain**: `rate_half_min_depth` and `rate_half_budget_exceeded` show that the
minimal depth is `t = 15` and that its transfer factor alone exceeds the budget, for every
value of the sub-Johnson constant.  The same holds for rate `1/4` at the second integer step.
This is a statement about *this* chain (shortening + sub-Johnson + binomial transfer), not
about the truth of the package's table.

**D59.5 (the certificates are conditional twice over).**  They assume both that
`SubJohnsonBoundPoly t C` holds and that the constant `C` is as small as the table requires
(down to `C ≤ 8` in the `1/8`, second-step row).  Neither is established here.

**Freeze list.**  Strong MCA definition unchanged; no slack-MCA; folded-RS capacity results and
the unconditional binomial post-Johnson bound untouched; no capacity-ordinary-RS work; no
axioms; no `sorry`/`admit`.

## 8.13 The sub-Johnson hypothesis was mis-shaped (run of 2026-08-24, second pass)

**D60.1 (the isolated hypothesis of §58 is false).**  `SubJohnsonBoundPoly t C` bounds the bad
set of a shortened generalised line by `C·(k+1)⁶`, a function of the dimension only.
`Root.CodingTheory.subJohnsonBoundPoly_false` refutes it for every `t` and `C`, by an explicit
dimension-one counterexample over a large prime field (see `RESULTS.md` §60.2).  Consequently
`ordinaryRS_badSet_postJohnson_of_subJohnson`,
`ordinaryRS_epsMCA_postJohnson_of_subJohnson` and the five certificates of
`PrizeCertificates.lean` are vacuous as stated.  They have been kept, with header notes, as a
record of the computation.

**D60.2 (what the literature actually claims).**  `J(N, d, E)` is a polynomial of degree at
most six in the **length**.  The corrected hypothesis `SubJohnsonBoundLen t C`
(`≤ C·(|D|+1)⁶`) is consistent with the counterexample and reproduces the Jo conclusion
`O_{r,h}(K⁶)` with the constant multiplied by `(2r)⁶`.

**D60.3 (the published `2⁻¹²⁸` table is not reachable over `q < 2²⁵⁶` through this chain).**
With the corrected numerator and constant `C = 1`, every row at `K = 2¹⁸` exceeds the `2¹²⁷`
budget — by `5` bits at rate `1/4` (first step) up to `17` bits at rate `1/2`
(`prize_budget_exceeded_rate_*`).  Certification succeeds over fields of size `2²⁶¹`–`2²⁷³`
(`prize_len_certificate_rate_*`).  Either the prime must be larger than the table's
`Q < 2²⁵⁶`, or the sub-Johnson bound must carry an explicitly sub-unit leading constant; the
incoming package supplies neither.

**D60.4 (unchanged from §8.12).**  The sub-Johnson bound itself — in either shape — is still
*not* proved in this project.  The claim that it follows from resultant elimination with no
non-degeneracy hypothesis remains refuted as a proof route (D59.1), and the corrected
statement remains an explicit hypothesis of every post-Johnson theorem here.

## 8.14 The affine factor split: what it does and does not settle (run of 2026-08-24, third pass)

**D61.1 (the discriminant route is dead, provably).**  `discLine_eq_zero_of_correlatedAgreement`
shows the discriminant of the formal-line interpolant vanishes identically whenever the line
has correlated agreement with a codeword pair on enough positions.  The hypothesis of
`card_badSet_le_disc` is therefore unsatisfiable in exactly the regime a proximity-gap theorem
must cover.  This joins `pairRes_eq_zero_of_mem_domain` as a proved barrier, not a suspicion.

**D61.2 (the split repairs the shape, not the conditionality).**  `card_badSet_le_affineSplit`
gives `|bad| ≤ (#Pairs)·|D| + (2·bY(R) − 1)·dZ(R)`: length-based, as BCHKS25 predicts, with
constants that the exact parameter search shows to be independent of the length.  But it still
carries a non-degeneracy hypothesis — now only on the residual factor `R` (`discLine bYR x₀ R ≠ 0`)
rather than on the whole interpolant.  The unconditional corner is
`card_badSet_le_affineSplit_linear` (residual linear in `Y`).

**D61.3 (mission targets T4–T6 are therefore not met unconditionally).**  The requested
`badSet_le_subJohnson_length` with *no* hypothesis, the unconditional
`ordinaryRS_badSet_postJohnson`, and the recomputed prize certificates are **not** claimed.
The missing ingredient is a transfer principle: from the existence of a low-`Z`-degree
interpolant over `𝔽_q` to the non-degeneracy of its residual factor at all but `O(n)`
specialisations.  Formally that is a Hilbert-irreducibility / specialisation statement about
the factorisation of `Q` over `𝔽_q[Z]`, and it is not present in Mathlib nor derived here.
No step of the present chain assumes it.

**D61.4 (the refuted forms stay refuted).**  Nothing here revives the dimension-based
`SubJohnsonBoundPoly`; `subJohnsonBoundPoly_false` is untouched, as are the folded-RS capacity
results, the binomial fallback and the strong MCA definition.

**D61.5 (the hypothesis is now a single, intrinsic statement).**  After
`exists_affine_split` and `card_badSet_le_affineSplit_discBiv`, the whole conditional content
of the affine-split chain is one statement: *the affine-factor-free residual of the canonical
split of the interpolant is squarefree in `Y`* (`discBiv bYR R ≠ 0`), together with the
schedule's degree bounds for that residual.  Repeated **affine** factors are handled
unconditionally.  What is not handled is a repeated **non-affine** factor: bounding the
parameters at which such a factor specialises to something with a low-degree root is a
Hilbert-irreducibility / Chebotarev statement for function fields, absent from Mathlib and not
derived here.  The degree bounds for the residual are stated as hypotheses rather than
inherited from the interpolant; they do follow from additivity of the `Z`- and `X`-degrees on
the polynomial tower, which is not formalised here.

## 8.15 The squarefree kernel does not remove the residual hypothesis (run of 2026-08-24, fourth pass)

**D62.1 (the incoming claim "no affine factor ⇒ squarefree in `Y`" is false).**  Refuted
formally by `Root.CodingTheory.exists_affineFactorFree_not_squarefree`, with the explicit
residual `(Y − Z²)²`, which has no affine linear factor `Y − (A + Z·B)` and whose `Y`-
discriminant vanishes identically.  The claim was *not* proved as stated in the brief; it was
disproved.

**D62.2 (the proposed squarefree-kernel containment is also false).**  The brief's target
"every bad `z` lies in the zero set of `Disc_Y(R_sf)`, of `Z`-degree `≤ (2b_Y(R_sf) − 2)d_Z(R)`"
fails for the same residual: `Disc_Y(R_sf) = 1` (no roots), while every parameter of the field
makes the specialised residual acquire a double root
(`Root.CodingTheory.sqfreeKernel_bound_fails`).  The failure is unbounded: over `ZMod p` the
locus has size `p` with kernel degrees fixed (`doubleRootLocus_card_unbounded`).  Consequently
the requested Lean targets T1–T3 of the mission cannot be proved in the requested form, and
T4 (`badSet_le_subJohnson_length` unconditional) does **not** follow from them.  Nothing in the
project assumes them.

**D62.3 (what is delivered instead).**  A factorwise bound
(`card_badSet_le_affineSplit_twoFactor`, `epsMCA_le_affineSplit_twoFactor`): for a residual
written as `R = R₁·R₂` the bad set is bounded under `Disc_Y(R₁) ≠ 0`, `Disc_Y(R₂) ≠ 0` and
`Res_Y(R₁,R₂) ≠ 0`.  Applied to `R_sf` and its cofactor, the resultant hypothesis is precisely
the statement that `R` has no repeated factor — so the residual hypothesis of §61 is localised
and made quantitative, not eliminated.

**D62.4 (status of the prize certificates is unchanged).**  The certificates continue to rest
on the same conditional length-based bound as before this pass (`SubJohnsonBoundLen` chain,
field sizes as recorded in §60–61), and the unconditional statements remain the pair-cover
bound and the unique-decoding / independent-folds chain.  No certificate was strengthened or
weakened here, no definition frozen by the mission brief was touched, and no axiom was added.

**D63.1 (the separable-kernel hypothesis is *not* necessary).**  Exact-arithmetic Phase 0
experiments (`analysis/explore_degenerate_residual.py`, 96 valid Guruswami–Sudan instances with
the GS root property verified) exhibit 27 instances in which the residual is non-squarefree in
`Y` *and* the line has no correlated agreement.  So the hypothesis is not automatic.  In all 27
the bad set has size 0–3, far below the licensed bound, and no instance without correlated
agreement violates the bound.  The hypothesis is therefore **sufficient but not necessary**:
its failure destroys the discriminant certificate, not the conclusion.  Any text that presents
squarefreeness of the residual as a lemma, or as necessary for the bound, is wrong on both
counts.

**D63.2 (degeneracy is an artefact of the canonical choice of `Q`).**
`analysis/space_of_interpolants.py` computes the whole `F_q(Z)`-space of interpolants obeying
the BCHKS25 degree bounds.  Where the minimal-`Y`-degree interpolant degenerates, 18–23 of the
19–25 sampled members of the same module are squarefree, and the module gcd is trivial on every
non-correlated-agreement instance.  A squarefree representative costs a constant factor in the
bad-locus degree (12→15, 18→24, 30→40 in the sampled configurations).  This does *not* prove
that a squarefree representative always exists; that statement is itself of
Hilbert-irreducibility type and is **not** assumed anywhere in the project.

**D63.3 (T3 of the Welch–Berlekamp brief is false).**  The proposed dichotomy step "a
degenerate pencil implies correlated agreement" is refuted.
`analysis/wb_dichotomy_counterexample_search.py` finds 12 exact counterexamples over
`q ∈ {41,61,101}`, all of the rational form `f₀ = P₀/Λ`, `f₁ = P₁/Λ` with `deg Λ ≤ e`, `Λ`
without roots in `D` and `Λ ∤ P₀`; `analysis/direct_bad_locus_from_syndrome.py` finds 11 more
of the same shape.  The refutation is now a theorem rather than a numerical observation: in
`RequestProject/Root/CodingTheory/WelchBerlekampPencil.lean`,
`Root.CodingTheory.wbDet_eq_zero_of_rationalLine` shows such a line degenerates *every* maximal
minor, while `Root.CodingTheory.not_isCloseOn_of_not_dvd` shows that when `k + 2e ≤ |D|` and
`Λ ∤ P₀` the word `f₀` is not even `e`-close to the code.  T3 is therefore **not** proved, and
nothing in the project depends on it.  What is delivered instead is the one-sided implication
`wbDet_eq_zero_of_correlatedAgreement` and the conditional bound
`card_badSet_le_of_wbDet_ne_zero`, whose hypothesis is an explicit, checkable non-degeneracy
condition on a concrete matrix.

**D63.4 (the syndrome/pencil test is vacuous above the unique-decoding threshold).**  In 84 of
84 instances with `2e ≥ n − k` the rank-drop set is all of `F_q`.  The formal counterpart is
`Root.CodingTheory.exists_nonzero_wbVector_of_card_lt`: when `|D| < k + 2e + 1` the
Welch–Berlekamp system has a nonzero solution for every word.  So this route cannot be pushed
past unique decoding, and no claim in the project suggests otherwise.

**D63.5 (subresultant probe is not yet evidence).**  `analysis/subresultant_bad_locus_check.py`
yielded only 9 usable instances out of 56 (the others are rejected by degree drop under
`Z`-specialisation, or have residual `Y`-degree `< 2`).  Containment and the degree bound hold
on all 9, but this sample is too small to support a claim, and the corresponding Lean targets
were **not** attempted on the strength of it.

## 8.16 The frontier after the Welch–Berlekamp pencil (consolidation pass)

This section records the state of the ordinary–Reed–Solomon strand at the close of the WB
pencil phase.  No new proofs were attempted in this pass; it is a frontier record.

**D64.1 (the unconditional ordinary-RS regime improves from `k + 3e ≤ |D|` to `k + 2e < |D|`).**
The project's previous unconditional line bound with constant `e + 1` was
`Root.CodingTheory.card_badSet_le_succ`, whose hypothesis is `k + 3e ≤ |D|`.  The WB pencil
gives the same constant on the *whole* unique-decoding regime `k + 2e < |D|`
(`card_badSet_le_of_wbDet_ne_zero`, `epsMCA_le_of_wbDet_ne_zero`), at the price of one
explicit non-degeneracy hypothesis — non-vanishing of a single maximal minor of a concrete
`(k+2e+1) × (k+2e+1)` matrix over `F[Z]`.  That hypothesis is a rank test on given data, not a
conjecture: it is decidable for any concrete instance.  Its failure is *implied* by correlated
agreement (`wbDet_eq_zero_of_correlatedAgreement`) but is not equivalent to it
(`wbDet_eq_zero_of_rationalLine` + `not_isCloseOn_of_not_dvd`), and above the threshold it
always fails (`exists_nonzero_wbVector_of_card_lt`).  Any text claiming a *hypothesis-free*
`e + 1` bound on `k + 2e < |D|`, or claiming that pencil degeneracy detects correlated
agreement, is wrong; the project claims neither.

**D64.2 (the single remaining ordinary-RS post-Johnson obstruction).**  On the
affine-factor-split route the entire conditional content is now one statement: *the
affine-factor-free residual `R` of the canonical split is squarefree in `Y`*, in Lean
`discLine bYR x₀ R ≠ 0`, the hypothesis of `Root.CodingTheory.card_badSet_le_affineSplit` and
`epsMCA_le_affineSplit`.  By `discLine_eq_zero_of_sq_factor` and
`no_sq_factor_of_discLine_ne_zero` this is exactly "the residual has no repeated factor
surviving the specialisation".  Nothing else on that route is open, and nothing else in the
project depends on it.

**D64.3 (the two candidate removals of D64.2 have not removed it).**  The squarefree-kernel
route is **refuted**, formally: `Root.CodingTheory.sqfreeKernel_bound_fails` and
`doubleRootLocus_card_unbounded` show that no function of the degrees of the squarefree kernel
can bound the double-root locus (`R = (Y − Z²)²` has kernel-based bound `0` and double-root
locus all of `F`).  The subresultant route remains a **probe only**: 9 usable instances out of
56 in `analysis/subresultant_bad_locus_check.py`, all passing, which is too thin to support a
claim and on the strength of which no Lean target was attempted.  What §62 does deliver is a
*factorwise* bound, `card_badSet_le_affineSplit_twoFactor`, which localises the hypothesis into
three checkable conditions but does not discharge it.

**D64.4 (empirical evidence is recorded, and nothing depends on it).**  The Phase 0
exact-arithmetic experiments (`analysis/explore_degenerate_residual.py`,
`analysis/space_of_interpolants.py`, `analysis/direct_bad_locus_from_syndrome.py`, and the WB
checks `analysis/wb_pencil_badset_check.py`, `analysis/wb_pencil_degree_check.py`,
`analysis/wb_dichotomy_counterexample_search.py`) are documented in `RESULTS.md` §63 and in
D63.1–D63.5 above.  They are exact-arithmetic evidence, not proof: **no theorem in the project
takes any of them as a hypothesis**, and in particular the observations "the bad set is small
even in the degenerate branch" and "a squarefree representative of the interpolation module
usually exists" are assumed nowhere.

## 8.17 The separable-component route (run of 2026-08-25)

**D65.1 The list-indexed reassembly is now formal, and it is a strict generalisation of the
two-factor one.**  `card_badSet_le_affineSplit_components` bounds the bad set of a line whose
interpolant splits into affine linear factors times `∏ i ∈ s, R i`, assuming only componentwise
separability in `Y` and pairwise coprimality in `Y`.  It reproduces
`card_badSet_le_affineSplit` (`#s = 1`) and `card_badSet_le_affineSplit_twoFactor` (`#s = 2`,
with the resultant term doubled because the sum runs over ordered pairs).

**D65.2 The brief's version with multiplicities is false.**  The requested bound for
`R = ∏ R_i^{e_i}` with `e_i ≥ 2` fails at every parameter for `R = (Y − Z²)²`; the refutation is
the project's own `sqfreeKernel_bound_fails` / `doubleRootLocus_card_unbounded`, and
`analysis/separable_component_counterexample_search.py` reproduces it numerically over
`F₅ … F₂₃`, together with counterexamples for dropping pairwise coprimality
(`(Y−Z)(Y−1)` and `(Y−Z)(Y−2)`) and for dropping separability (`Y^p − Z` in characteristic `p`,
whose formal discriminant vanishes identically, so the certificate is empty).  Nothing in the
project assumes the false version; what is formalised is the multiplicity-free list.

**D65.3 The success criterion "the bound no longer assumes the whole residual is squarefree" is
met only syntactically.**  Since `Disc(fg) = Disc(f)·Disc(g)·Res(f,g)²`, the componentwise
hypotheses imply that the whole residual is squarefree in `Y` at `x₀`; the check
`analysis/separable_component_check.py` confirms this in 750/750 admissible instances (column
`C5`).  The route therefore *localises and makes checkable* the residual hypothesis — one
condition per component, each about a single irreducible-size object — but it does not weaken
it.  A genuinely weaker hypothesis would have to control repeated factors, which D65.2 shows no
discriminant/resultant certificate can do.

**D65.4 The post-Johnson statement is conditional, and the condition is explicit.**
`ordinaryRS_badSet_postJohnson_separable` is proved from `SeparableComponentSplit r h a`, which
asserts the *existence* of the split with degree budgets `a·K`, `a·K²` over fields with
`a·K² ≤ |F|`.  That hypothesis is not proved here, and its hard half — the existence of a good
specialisation point `x₀` for all components at once — is exactly the counting statement that
the external forks also leave conditional (see `analysis/RESOURCE_INVENTORY.md`).  What is new
is that, granted it, the conclusion is a clean `C·K⁶` with `C = a·r + 2a³ + 2a⁴` and a
`2⁻¹²⁸` certificate at `|F| ≥ 2²³⁶·C` for `r = 2`, `K = 2¹⁸` — better than the `2²⁶¹ … 2²⁷³` of
the shortening chain (D60), because no `(2r)^t·binomial` factor is paid.

**D65.5 Frozen items untouched.**  No change to the strong MCA definition, the folded-RS
capacity results, the binomial fallback, or the earlier refutations; no axioms were added; the
whole project builds sorry-free.

## 8.18 Good specialisation points (run of 2026-08-25, continued)

**D66.1 The hard half of D65.4 is now proved, from an explicit counting hypothesis.**  D65.4
recorded that the existence of a single good specialisation point `x₀` for all components at
once was left conditional (as in the external forks).  `exists_good_specialisation` proves it:
if the components are separable in `Y` and pairwise coprime in `Y` over `F(Z)(X)` and

    ∑_i (2b_i − 1)·d_X + ∑_{(i,j) ∈ offDiag} (b_i + b_j)·d_X < |F| ,

a good `x₀` exists.  What remains conditional in
`ordinaryRS_badSet_postJohnson_separableBiv` is only the *structural* half — that the
interpolant does split into affine linear factors times a multiplicity-free separable,
pairwise-coprime component list with the schedule budgets.  No specialisation point occurs in
the hypothesis any more.

**D66.2 The Lean counting hypothesis is weaker than necessary by a factor of two on the
resultant term.**  The informal bound sums over unordered pairs `i < j`; the Lean statement
sums over `s.offDiag`, i.e. over ordered pairs, and so demands twice as much.  This is a
deliberate simplification (`offDiag` is the index set already used by the §65 bound) and is
conservative: it only strengthens the hypothesis.  `analysis/good_specialisation_check.py`
reports both forms and finds the sharper one valid in all 175 instances.

**D66.3 The zero-test of the validation script is grid-based, hence bounded.**  A certificate
is declared zero when it vanishes on all of `F_q × F_q`; this is sound only below degree `q`,
so instances whose degree bounds reach `q` are skipped (65 of 240) rather than misreported.
The Lean proof has no such restriction.

**D66.4 The prize certificate is unchanged.**  The counting hypothesis is `O(K⁵)` while the
soundness requirement is `O(K⁶)`; at `r = 2`, `K = 2¹⁸` the latter dominates, so
`separable_prize_certificate_biv` needs the same `|F| ≥ 2²³⁶·C` as
`separable_prize_certificate`.  Removing `x₀` from the hypotheses costs nothing in field size.

**D66.5 Frozen items untouched.**  No change to the strong MCA definition, the folded-RS
capacity results, the binomial fallback, or the earlier refutations; no axioms; the whole
project builds sorry-free, and every new declaration is audited in `RequestProject/Main.lean`
to `[propext, Classical.choice, Quot.sound]`.

**D67.1 The requested implication `inseparable ⟹ R = S^p` is false, twice over.**  The
mission's proof sketch for `no_inseparable_factor_of_slack` proposed: inseparable ⟹ zero
`Y`-derivative ⟹ `R = S^p` over the perfect field `F_q` ⟹ contradiction with minimality.
Neither step survives.  (i) `R` is assumed *irreducible*, and an irreducible element is
never a proper power (`not_isPow_of_irreducible`), so the implication is self-contradictory.
(ii) The relevant coefficient field is not `F_q` but `L = F_q(Z)(X)`, which is *imperfect*;
zero derivative gives only `R = expand p S`, i.e. `R ∈ L[Y^p]`
(`exists_expand_of_not_separableInY`), and `Y^p − Z` is an irreducible element of `L[Y^p]`
(`inseparableWitness_irreducible`, by Eisenstein at the prime `Z`) which is inseparable and
not a power.  The minimality route is therefore closed; the honest criterion is the
characteristic bound.

**D67.2 What replaces it, and why it is free.**  `no_inseparable_factor_of_slack` is proved
under `bY < ringChar F`, where `bY` is the interpolation step's own `Y`-degree budget
(`(L−1)/k`, a small constant).  For every field of interest — `M31 = 2³¹ − 1`, BabyBear,
Goldilocks, any large prime field — this is satisfied by many orders of magnitude.  It is
*necessary*: `exists_irreducible_not_separableInY` exhibits an irreducible inseparable
factor of `Y`-degree exactly `ringChar F`, and
`analysis/inseparable_factor_slack_check.py` (Part B) shows that multiplying a genuine
interpolant by it keeps every interpolation condition.

**D67.3 The minimality field exists but does not help.**  `exists_minimal_lineInterpolant`
adds the requested minimality for free (well-ordering), and
`analysis/lexicographic_minimality_check.py` confirms that the interpolant the project uses
is of minimal `Y`-degree in 20/20 tested instances.  What minimality buys is a bound on
`deg_Y Q` — which is exactly what makes D67.2 free — and nothing else: it does not exclude
inseparable factors by itself (D67.1), and it does not give squarefreeness (D67.4).

**D67.4 The one genuinely remaining hypothesis is squarefreeness of the concrete `Q`
(the case `e_i > 1`).**  The factorisation `Q = C·∏ R_i^{e_i}` is now a theorem, and so is
separability of the `R_i`.  What is *not* proved is `e_i = 1`.  This matters: with a
repeated component the summed bad-set bound is false, and this project already refutes it
(`sqfreeKernel_bound_fails`, `doubleRootLocus_card_unbounded`, witness `(Y − Z²)²`).
BCHKS25 delegates the case `e_i > 1` to [BCI⁺20, Appendix C]; that appendix is *not*
formalised here.  Empirically the case does occur for the concrete minimal-degree
interpolant: 4/185 in `analysis/factorisation_slack_Q_check.py`, 27/96 in the earlier
`analysis/phase0_experiment1_output.txt`, and `analysis/phase0_experiment2_output.txt`
exhibits whole modules in which no sampled interpolant is squarefree.  Hence the
post-Johnson chain is stated under `SquarefreeInterpolantSplit` and is *not* unconditional.
The precise missing step is: *for the interpolant produced by the slack/GS construction at
the post-Johnson radius, either `e_i = 1` for all `i`, or the bad-set count can be run on
the separable kernels (BCI⁺20, Appendix C)*.

**D67.5 The hypothesis actually removed.**  Compared with §66, `SeparableComponentSplitBiv`
(affine split + component list + `discBiv ≠ 0` + pairwise `resBiv ≠ 0` + per-component
budgets) is gone, replaced by `SquarefreeInterpolantSplit` (one squarefree interpolant with
three degree budgets) plus the explicit `a·K < ringChar F`.  The constant improves from
`a·r + 2a³ + 2a⁴` to `2a³ + 2a⁴`.

**D67.6 Frozen items untouched.**  No change to the strong MCA definition, no weakening to a
slack MCA, no removal of the folded-RS capacity results or of the binomial fallback, no new
axioms, no `sorry`.  All new declarations are audited in `RequestProject/Main.lean` and
depend only on `[propext, Classical.choice, Quot.sound]`.

## 8.19 Multiplicity elimination: what the carrier route settles and what it does not (run of 2026-08-26)

**D68.1 D67.4 is weakened, not closed.**  The open item D67.4 was squarefreeness of the
non-affine part of the concrete interpolant (the case `e_i > 1`).  §68 replaces it with
`DoubleRootTransfer` / `TransferInterpolantSplit`: instead of `Q` being squarefree, one asks
for a squarefree *carrier* `S` of the double roots of `Q`, i.e. every `(Y − p)²` (with
`deg p < k`) dividing a specialisation of `Q` already divides the same specialisation of `S`.
`transferInterpolantSplit_of_squarefreeInterpolantSplit` proves this is implied by the §67
hypothesis, so the frontier moved strictly outward, and the constants
`(2a³ + 2a⁴)·K⁶` are unchanged.  But the post-Johnson ordinary-RS theorem is still
**conditional**: `card_badSet_postJohnson_transfer` takes `TransferInterpolantSplit` as a
hypothesis.  No unconditional post-Johnson claim is made.

**D68.2 The literal T3/T4 mechanism requested in the mission is refuted.**  The mission asked
for `badSet_subset_roots_gcdDerivative` plus `gcdDerivative_degree_bound`, i.e. that the bad
parameters are roots of the `Z`-projection of `gcd_Y(Q, ∂_Y Q)` and that the reduced part
carries the count.  The exact-arithmetic search
`analysis/multiplicity_elimination_counterexample_search.py` found **8 counterexamples in 120
scanned instances**: `gcd_Y(R, ∂_Y R)` is nontrivial, yet the bad parameters have
multiplicity 2 in `R_z` and multiplicity 1 in the reduced specialisation `R_red,z`, so the
discriminant of the reduced part does not vanish at them.  All are of shape `R = c·S²`
(`deg_Y R = 2`, `deg_Y R_red = 1`); a fully explicit one is recorded in RESULTS §68.6.  The
Lean counterpart is `doubleRootTransfer_reducedPart_fails`, proved from the witness
`(Y − Z²)²`.  Per the mission's stop rule, the mechanism is reported as incomplete and the
conditional frontier is kept.

**D68.3 The line-trace count is vacuous, provably.**  The alternative counting route through
the trace `Z ↦ Q(x, f₀(x) + Z·f₁(x))` is formalised in full
(`lineTrace`, `eval_lineTrace`, `natDegree_lineTrace_le`, `eval_lineTrace_eq_zero_of_dvd`,
`card_badSet_le_lineTrace`), but its counting hypothesis can never be met on a genuine
interpolant: `lineTrace_eq_zero_of_lineInterpolant` proves that the interpolation condition
forces the trace to vanish at *every* position of `D`.  The exact-arithmetic run reports the
same for the residual — `|U| = 0` in 66/66 instances, with the residual non-squarefree in
27/66.  The theorem is retained as a documented dead end, not as a step in the chain.

**D68.4 The requested T1 iff had to be restricted.**  The mission's
`multiplicity_gt_one_iff_gcd_derivative_nontrivial` is false as stated over the coefficient
field in play: `F(Z)(X)` is imperfect in characteristic `p`, and `Y^p − Z` is irreducible
with vanishing `Y`-derivative, so a nontrivial `gcd_Y(Q, ∂_Y Q)` does not imply a repeated
factor.  `sq_dvd_iff_not_separable` is therefore stated under `[PerfectField K]`; the
unrestricted direction `R² ∣ Q → R ∣ ∂Q` (`dvd_derivative_of_sq_dvd`) holds over any
commutative ring and is the one actually used.

**D68.5 Method constraints observed.**  No Hensel lifting, no Fitting ideals, no
subresultants, and no global squarefree assumption are used; the proofs use only
divisibility, derivatives, discriminants of the line specialisation, degree bounds and root
counting.  Validation was exact (integer/`Fraction`) arithmetic throughout, no floats.

**D68.6 Frozen items untouched.**  No change to the strong MCA definition, no weakening to a
slack MCA, no removal of the folded-RS capacity results or of the binomial fallback, no new
axioms, no `sorry`.  All 25 new declarations are audited in `RequestProject/Main.lean` and
depend only on `[propext, Classical.choice, Quot.sound]`.

**D68.7 The obstruction now has an unconditional name.**  `card_badSet_le_repeatedPart`
bounds the bad set, with *no* multiplicity hypothesis, by the affine term plus the
discriminant term of the surviving part plus `|codewordLocus k G|`, the number of parameters
at which a candidate codeword is a root of the repeated part `G`.  This is unconditional and
it replaces the qualitative statement "the case `e_i > 1` is open" by a single quantity to be
bounded.  It also shows that no bound is available from algebra alone: for `G = Y − Z²` the
codeword locus is all of `F`, since `p = z²` is a root of `G|_{Z=z}` at every `z`.  Any proof
of the missing step must therefore use the agreement/decoding hypothesis, not merely gcd,
derivative, resultant and degree data — which is consistent with the refutations D68.2 and
D68.3 and with the reported structure of [BCI⁺20, Appendix C].

## 8.20 Unique decoding by double counting (run of 2026-08-26, second pass)

**D69.1 The requested T4 is false as stated.**  The mission asked for
`2e < N − k ⟹ #bad ≤ 1`.  For the project's **strong** bad set — `γ` is bad when *some* set
`S` with `|S| ≥ |D| − e` witnesses closeness of the line word at `γ` but not of the pair —
this is refuted, both numerically (112 instances out of 826) and in Lean
(`not_forall_card_badSet_le_one`, an explicit `F₇` witness with two bad parameters at
`2e = 2 < 5 = |D| − k`).  The reason is that badness quantifies existentially over the
witness set `S`, so two different `S`'s may certify two different bad parameters even below
the unique-decoding radius.  The freeze list forbids weakening the definition, so the claim
was corrected rather than the definition.

**D69.2 The corrected statement, proved and sharp.**  `card_badSet_le_succ_radius` gives
`#bad ≤ e + 1` in the regime `3e < |D| − k + 1`, and the `F₇` witness of D69.1 (where
`e + 1 = 2`) shows the constant cannot be lowered.  The proof is exactly the requested double
count on pairs `(γ, x)`: T1/T2 are `exists_correlatedAgreement_of_two_goodZ`, T3 is
`exists_mem_polyAgreement_sdiff_of_isBad` together with the disjointness supplied by
`mem_inter_polyAgreement_of_mem_two`, and T4 is replaced by the corrected count.

**D69.3 Regime gap.**  The proved bound needs `3e < |D| − k + 1`, not merely
`2e < |D| − k`; the extra factor comes from `eval_eq_add_smul_of_close`, which identifies a
local witness with `q₀ + γ·q₁` and consumes `2e` from the correlated pair plus `e` from the
witness itself.  The search reports no violation of `#bad ≤ e + 1` in the intermediate band
either (`S4 = 0`, 0 failures), so the bound is plausibly true under `2e < |D| − k` alone; this
is recorded as **open**, not claimed.

**D69.4 Reuse, not duplication.**  Nothing new was added to `MCA.lean`: the section reuses
`IsCloseOn`, `LineCloseOn`, `IsBad`, `badSet`, `goodZ`, `line_closure`,
`mem_goodZ_of_isBad`, `eval_eq_add_smul_of_close`, `card_polyAgreement_lineComb_ge`,
`mem_inter_polyAgreement_of_mem_two`, `correlated_agreement_of_two` from
`ProximityGapLines.lean`, `eval_eq_of_card_agreement_ge` from `MCAJohnson.lean`, and
`exists_codewords_of_lineCloseOn` from `LineDecodable.lean`.  The earlier
`card_badSet_le` (bound `|D|`, same regime) is left in place and is now superseded in
strength by `card_badSet_le_succ_radius`.

**D69.5 Frozen items untouched.**  No change to the strong MCA definition, no weakening to a
slack MCA, no removal of the folded-RS capacity results or of the binomial fallback, no
attempt at capacity ordinary RS, no new axioms, no `sorry`.  All eight new declarations
depend only on `[propext, Classical.choice, Quot.sound]`.

**D70.1 The `2e` weakening is false, and D69.3 must be read precisely.**  D69.3 recorded as
*open* the possibility that `#bad ≤ e + 1` holds under `2e < |D| − k`.  The mission of this
run asked about the weaker hypothesis `2e < |D| − k + 1`.  These are different: the second
admits `2e = |D| − k`.  Exactly that boundary case is now refuted
(`not_forall_card_badSet_le_succ_radius_of_two_radius`), while D69.3's strict version
`k + 2e < |D|` survives every exhaustive scan performed here.  The distinction is not
cosmetic: the strict version is the Welch–Berlekamp regime, and the refuted version is not.

**D70.2 The refutation is stronger than requested.**  The witness has `#bad = |D|`, i.e. the
trivial bound `card_badSet_le` is attained in the band `2e < |D| − k + 1 ≤ 3e`.  Hence no
bound depending on `e` alone can hold there, and `card_badSet_le_succ_radius` is optimal in
its hypothesis, not merely unproved beyond it.

**D70.3 The witness is invisible to the pencil, too.**  `GapWitness.wbDet_eq_zero` shows every
maximal minor of the Welch–Berlekamp pencil of the witness vanishes identically — forced,
since `k + 2e = |D|` there.  Combined in
`card_badSet_le_succ_radius_of_count_or_pencil`, the two available unique-decoding criteria
leave exactly one hole: `k + 2e < |D|` with a totally degenerate pencil.

**D70.4 Smooth domains do not help the line bad set.**  A frequently voiced expectation is
that a 2-adic subgroup domain (the FFT/FRI setting) improves MCA counts.  The exact probe
`analysis/badset_smooth_domain_probe.py` finds the same worst case `#bad = |D|` for subgroup,
coset and generic domains.  Smoothness pays through folding, not through the plain line MCA.

**D70.5 Frozen items untouched.**  No change to the strong MCA definition, no weakening to a
slack MCA, no removal of folded-RS capacity results or of the binomial fallback, no attempt at
capacity ordinary RS, no new axioms, no `sorry`.

---

**P34 (new, proved) The strict unique-decoding window is refuted.**
`Root.CodingTheory.not_forall_card_badSet_le_succ_radius_strict_window`
(`RequestProject/Root/CodingTheory/StrictWindowRefutation.lean`): over `ZMod 11` with
`D = {0,1,2,3,4,5,9,10}`, `k = 3`, `e = 2` (so `k + 2e = 7 < 8 = |D|`) the line
`f₀ = 1_{0} + 1_{3}`, `f₁ = 1_{0} + 3·1_{1} + 3·1_{2} + 1_{3}` has the four bad parameters
`0, 1, 8, 10`.  Kernel-checked; `#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound`.  This closes, negatively, the conjecture
`badSet_card_le_e_plus_one_strict_window` of the Strand-1 mission; no proof was attempted
after the counterexample appeared, as instructed.

**O29 (closed) The hole in `card_badSet_le_succ_radius_of_count_or_pencil`.**  That docstring
recorded "`k + 2e < |D|` together with a totally degenerate pencil" as the one case left open
between the counting route and the Welch–Berlekamp route.  `StrictWindowWitness.wbDet_eq_zero`
shows the new witness has a totally degenerate pencil while satisfying `k + 2e < |D|`, so the
open case is settled: neither hypothesis can be dropped, and their disjunction is not
exhaustive.

**D71.1 Earlier scans were not wrong, only too small.**  `analysis/badset_wb_regime_probe.py`
had scanned the strict window exhaustively at `q = 7`, `|D| = 6`, `k = 1`, `e = 2`
(14 412 000 instances, `max #bad = 3`).  The structure theory in
`analysis/strict_window_counterexample_search.py` explains this: a counterexample needs
`|T| = k + 1 ≥ 4`, hence `k ≥ 3`, `|D| ≥ 8`, `q ≥ 8`.  The new Phase-2 scan also shows the
event has codimension 2 in the space of lines, so random sampling is a poor detector.

**D71.2 What is *not* claimed.**  The refutation concerns the project's strong bad set at
these parameters.  It says nothing about slack/GG25 variants, nothing about folded RS, and it
does not weaken `card_badSet_le_succ_radius`, whose hypothesis `3e < |D| − k + 1` is now known
to be optimal in both directions (boundary `k + 2e = |D|`: `GapWitness`; strict window
`k + 2e < |D|`: `StrictWindowWitness`).

---

**P35 (new, proved) First syndrome/MDS certificate at `ρ = 1/2`.**
`Root.CodingTheory.epsMCAmax_le_rho_half_circuit`
(`RequestProject/Root/CodingTheory/RhoHalfSyndromeCertificate.lean`): `|D| = 2²⁰`, `k = 2¹⁹`,
`e = 314572`, `|F| ≥ 2⁶⁹⁹¹⁸⁰` gives `ε_mca ≤ 2⁻¹²⁸`, together with the converse
`circuit_field_size_ge_rho_half` (`≥ 2²⁰⁹⁷¹⁴`), i.e. a two-sided bracket for what the
circuit-incidence route can deliver.  Kernel-checked, no new axioms.

**D72.1 The mission parameters are internally inconsistent.**  The brief asked for
`n = 2²⁰`, `k = 2¹⁸` *and* `ρ = 1/2`; but `2¹⁸/2²⁰ = 1/4`.  Both readings are recorded:
`epsMCAmax_le_rho_half_circuit` / `epsMCAmax_le_rho_half_counting` use `k = 2¹⁹` (true rate
`1/2`), and `epsMCAmax_le_rho_quarter_counting` uses the literal `k = 2¹⁸`.

**D72.2 The certificate is not a post-Johnson claim.**  `δ = 0.2999992…` is above the Johnson
radius for `ρ = 1/2`, but the required field size `2⁶⁹⁹¹⁸⁰` grows exponentially in the block
length.  No capacity claim, no post-Johnson claim, and no practical parameter set is asserted.
The bracket is also loose: the exact constant has bit length 415043 versus the proved bracket
`[209714, 699052]`.

**D72.3 Numeral-heavy Lean goals.**  With terms such as `2^524288` in the goal, `ring`/`norm_num`
and single large proof terms fail with `maximum recursion depth` / `(kernel) deep recursion
detected`.  The working pattern (used throughout the new file) is: abstract-variable assembly
lemmas plus one top-level theorem per concrete step.

---

**P36 (new, proved) The monomial sharpening `#Bad ≤ 1` fails on three cosets.**
`Root.CodingTheory.not_forall_monomial_card_badSet_le_one`
(`RequestProject/Root/CodingTheory/MulticosetMonomialWitness.lean`): `ZMod 13`,
`D = {±1, ±2, ±3}`, `k = 2`, `e = 1`, `f₀ = t⁴`, `f₁ = t⁵`, bad set `{1, 12}`.

**D73.1 The "established facts" of the mission brief are not in this repository.**  The brief
cites `RequestProject/MCAMonomialSharp.lean` (a proved `#Bad ≤ 1` for monomial packets on a
cyclic root domain under `3e + m ≤ N`) and `RequestProject/MCAMultilayer.lean` (an `L = 3`
counterexample over `ZMod 5`).  Neither file exists here, and no declaration of that content
is present (`rg -l "monomial"` finds only unrelated material).  Consequently the monomial
claim was *not* assumed: it was re-tested from scratch inside this project's own definition of
the strong bad set, and it holds in the whole scanned range for one and two cosets
(269 834 instances) while failing for three (explicit formalized witness).

**D73.2 What the scans do and do not support.**  Supported in the scanned range: `#Bad ≤ 1`
for `s ≤ 2` cosets, `#Bad ≤ s` for `s ≤ 3`.  Not supported and not claimed: any statement for
`s ≥ 4`, for binomial packets, for multilayer (`L ≥ 3`) packets, or for larger fields than
`q ≤ 31`.  `#Bad ≤ s` is recorded as an open conjecture, not as a theorem.

**D73.3 Circle-STARK interface.**  `CIRCLE_STARK_INTERFACE_AUDIT.md` records the static audit:
the circle development (`RequestProject/Circle*.lean`) and the MCA development
(`RequestProject/Root/CodingTheory/`) are disjoint, the circle twin-coset domain is a union of
two cosets of `⟨q⁴⟩` *in the circle group*, and the missing piece for any application theorem
is a circle-code definition together with its bridge to univariate RS.  No Circle-STARK
certificate is claimed.

---

**P37 (new, proved) The structured second layer.**
`Root.CodingTheory.card_badSet_le_one_of_structured_snd`
(`RequestProject/Root/CodingTheory/StructuredSecondLayer.lean`): if `f₁` is the evaluation of
one polynomial `g` with `k ≤ deg g < t` and `2e + t ≤ |D|`, then `#Bad ≤ 1`, with no
hypothesis on `f₀`.  Companion: `badSet_eq_empty_of_codeword_snd` (`deg g < k` ⇒ `#Bad = 0`).

**D74.1 The degree window is essential, not a technical convenience.**  The proof needs
`deg (g − q₁) < t` together with `t ≤ |T|` on the common agreement set, and `t ≤ |D| − 2e`.
Both bounds are used: without `deg g < t` the root count is not decisive, and without
`k ≤ deg g` the conclusion is `#Bad = 0` rather than a contradiction.  The three-coset
counterexample P36 lies exactly *outside* the window — there `deg g = 5` while
`t ≤ |D| − 2e = 4` — so it is not a counterexample to P37; the two results are consistent and
together they show the window cannot simply be dropped.  What is **not** proved is sharpness of
either boundary (`deg g = k−1` vs `k`, `deg g = t−1` vs `t`): no boundary witness is
formalized, and none is claimed.

**D74.2 The `ρ = 1/2` structured certificate is a per-line statement.**
`epsMCA_le_two_pow_neg_128_structured_rho_half` bounds `ε_mca` of a line whose second layer
satisfies the structural hypothesis; it is *not* a bound on `epsMCAmax` (the maximum over all
lines).  `δ ≈ 0.2499990 < 1/4` is inside the unique-decoding radius at `ρ = 1/2`, so no
post-Johnson and no capacity claim is made.  The comparison with the `δ = 1/6`, `|F| ≥ 2¹⁴⁶`
certificate of P35/§72 is therefore a comparison of *different* statements: the earlier one is
unconditional over all lines, the new one is conditional on the second layer.

**P38 (new, proved) The FRI radix-2 fold supplies the structural hypothesis.**
`Root.CodingTheory.friSnd_eval` (`RequestProject/Root/CodingTheory/FRIFoldStructured.lean`):
the second layer of one FRI round applied to the evaluation of a single polynomial `P` is the
evaluation of `oddPart P`, of degree `⌊(deg P − 1)/2⌋`.  Hence
`fri_fold_badSet_eq_empty_of_low_degree`, `fri_fold_card_badSet_le_one`, `fri_fold_epsMCA_le`
and the concrete round `fri_round_epsMCA_le_two_pow_neg_128`.

**D75.1 The FRI theorems assume a single-polynomial prover.**  The hypothesis is that the
*tested word* is `x ↦ P.eval x`; an unrestricted prover sends an arbitrary vector, for which
only `#Bad ≤ e + 1` is available.  The statements quantify over an arbitrary first layer, so
nothing is assumed about the even part, but the restriction on the word itself is real and is
not hidden in the certificate.

**D75.2 The square-root section is a hypothesis, discharged for the FRI geometry.**  The layers
are defined through `σ` with `σ(y)² = y`, `σ(y) ≠ 0`; `exists_sqrt_section` shows such a `σ`
exists whenever the folded domain is the squaring image of a domain avoiding `0`, which is the
FRI situation.  Characteristic `2` is excluded (`(2 : F) ≠ 0`), as it must be.

**D76.1 Circle-STARK: the audit result is negative and unchanged.**  Re-audited after P37/P38
(`RESULTS.md` §76).  The concrete failing condition is *not* one of the degree inequalities:
the repository contains no circle code and hence no circle bad set, so the hypotheses cannot
even be stated for the circle protocol.  Missing, in order: the circle code on a twin coset,
the 2-to-1 `x`-projection into even/odd univariate RS parts, the identification of the circle
fold's second layer with the odd part.  No Circle-STARK certificate is claimed.

**P39 (new, proved) `#Bad ≤ s` is false.**
`Root.CodingTheory.not_forall_monomial_card_badSet_le_three_cosets`
(`RequestProject/Root/CodingTheory/MulticosetSharpSliceWitness.lean`): `ZMod 17`,
`D = H ∪ 2H ∪ 3H` with `H = {1,4,13,16}`, `k = 2`, `e = 3`, `f₀ = t⁸`, `f₁ = t⁹`, bad set
`{6,7,10,11}`, so `#Bad = 4 > 3 = s` inside the regime `3e + k ≤ |D|`.  This **supersedes
D73.2**: the coset-count conjecture recorded there as open is now refuted.  The slice scan
that found it (`analysis/multicoset_monomial_sharp_slice.py`, `q ∈ {5,…,29}`, 68 363 instances
in the slice `e + 1 > s`) is complete for those primes; `q = 31` was not run and no claim is
made for it.

**D78.1 The circle code exists only as a scratch probe, not in the repository.**  The closing
feasibility question ("can the circle code be defined in 15–20 lines?") was answered by
elaborating a candidate `Submodule F (↥D → F)` in a scratch file (`RESULTS.md` §78.2,
`CIRCLE_STARK_INTERFACE_AUDIT.md` §7).  That candidate is **not** part of the repository and
nothing is proved about it — in particular no minimum-distance bound, hence no circle bad set,
hence no `ε_mca`.  Any later reader should treat the code block in the audit as a sketch of a
future interface, not as a declaration of this project.  D76.1 stands unchanged.

**D78.2 What "unconditional" means for the one-round certificate.**  `RESULTS.md` §78.1 calls
`fri_round_epsMCA_le_two_pow_neg_128` unconditional *given the fold hypothesis*.  Precisely:
no hypothesis is placed on the first layer, on the challenge, or on the structure of the second
layer (the latter is proved, D75.1/P38); the hypotheses that remain are that the tested word is
the evaluation of a single polynomial of the stated degree, that the domain admits a square-root
section (D75.2), and the numeric parameter constraints.  It is one round of one line — no
multi-round composition and no bound on `epsMCAmax` is claimed.

## 8.21 The circle bridge (run of 2026-08-27)

**D79.1 — "the circle second layer is an ordinary polynomial `g(x)`" is false for the circle
code.**  A circle word `a(x) + y·b(x)` takes two different values on the two points of an
`x`-fibre whenever `b(x) ≠ 0`; first counterexample in
`analysis/circle_bridge_falsification.py` (T1).  Any earlier expectation that
`StructuredSecondLayer` instantiates directly at the circle code through an ordinary polynomial
is therefore unfounded, and no such statement is made.

**D79.2 — the folded instance is not the circle instance.**  After the `J`-fold the second
layer *is* an ordinary polynomial on the projected domain (T2, 0 failures), but the strong MCA
quantity of the folded univariate instance differs from that of the circle instance built from
the same layers (T6: 35 of 80 differ, separating examples in both directions).  So §75 does not
transfer to the circle code by folding, and the circle statement had to be proved directly.

**D79.3 — characteristic 2 is a genuine obstruction, not a convenience.**  Over `F₂` the
polynomial `1 − X²` is a square, the norm of `(1 + X) + y·1` is identically zero, and that
nonzero word vanishes on the whole circle; the zero-count hypothesis fails outright.  All
circle statements carry `(2 : F) ≠ 0`.

**D79.4 — the slack `+1` is necessary.**  With `2e + 2t' = |D|` (one short of the hypothesis)
there is an explicit instance with `#Bad = 2`: `q = 31`, `|D| = 8`, `k = 2`, `t' = 3`, `e = 1`,
`a = 18 + 19X + 3X²`, `b = 24 + 18X + 5X²`, bad set `{0, 19}`.  This is the circle analogue of
the univariate boundary already recorded (`2e + t = |D| + 1` breaks the window).

**D79.5 — minimum distance does not imply the structured conclusion.**  In the unique-decoding
regime `3e < d` of the circle code an unstructured second layer can still have `#Bad = 2`
(`q = 31`, `|D| = 8`, `k = 2`, `d = 4`, `e = 1`).  Distance-only reasoning gives the generic
`n/|F|`, not `1/|F|`.

**D79.6 — scope.**  What is proved is a *per-line* statement about the circle code with a
structured second layer: a single round, a single line, no claim about `ε_mca` maximised over
all lines, no claim about a circle FRI protocol or Circle-STARK soundness.  The counterexample
of D79.2 is the reason no protocol-level transfer is asserted.

**D79.7 — reuse audit.**  `Alphabet.badSet_eq_empty_of_snd_mem` is a strict strengthening of
the pre-existing `Alphabet.badSet_eq_empty_of_mem` (`CurveDecodability.lean`), which requires
both layers to be codewords; both are kept.  The new theorem
`Alphabet.card_badSet_le_one_of_zeroCount` reuses `Alphabet.correlatedAgreement_of_two` and
`closeTo_of_agreeOn` unchanged; the strong `Bad` definition was not touched.

## D80.1 — scope of the one-round Circle-FRI certificate

`circle_fri_one_round_epsMCA_le_one_div` and its `2⁻¹²⁸` instance are statements about **one**
fold, **one** line of words, and a prover word of the form `a(x) + y·b(x)`.  They say nothing
about: several FRI rounds, the composition of rounds, words that are not of that form (there
only the counting bound `#Bad ≤ e + 1` is available), or any Circle-STARK protocol.  In
particular no multi-round soundness and no capacity statement is implied.

## D80.2 — the fold is only defined away from the fixed points

The second layer of the inversion fold divides by `(σ u).y`.  At a fixed point of `J`
(i.e. `y = 0`, the points `(±1, 0)`) the numerator vanishes identically and `b` is not
determined by the word.  The Lean statements therefore carry `(σ u).y ≠ 0`, and
`exists_circleFoldSection` derives it from `∀ p ∈ D, p.y ≠ 0`.  Twin-coset Circle-FFT domains
satisfy this, but an arbitrary circle domain need not.

## D81.1 — what the generality checkpoint does and does not establish

`Alphabet.card_badSet_le_one_of_zeroBounded` is a single mechanism covering all four `#Bad ≤ 1`
certificates in the project, and `zeroBounded_iff_minDistGe` identifies its hypothesis as a
minimum-distance statement.  This is a statement about *proof structure*, not a new bound: the
mechanism consumes a minimum-distance bound and cannot produce one, it needs `f₁ ∈ V` (supplied
per fold by a prover-word lemma), and it is confined to `2e + t ≤ |ι|`, i.e. inside unique
decoding.  Nothing here bears on the capacity regime.

## D82.1 — the new list-size theorem is still unique decoding

`card_badSet_le_hammingDistance` gives `#Bad ≤ L` with `L > 1`, but its hypothesis
`2e + 2·d(f₁,q) < d` forces `d(f₁,q) < d/2`, so `q` is the unique nearest codeword.  The
theorem extends the *coverage* of the mechanism (to second layers close to the code), not its
decoding radius.  Nothing here is a Johnson-radius or capacity statement, and no radius
computation beyond `2e` is claimed.

## D82.2 — `#Bad ≤ max(1, L·2e)` — RESOLVED: now proved (see D83.1)

`ZERO_LOCUS_FRONTIER.md` §8 recorded this as a conjecture supported by 783 830 scanned
instances.  It is now a Lean theorem,
`Alphabet.card_badSet_le_two_mul_mul_card_nearbyList` (§83 of `RESULTS.md`), together with the
sharper `#Bad ≤ max(1, ∑_{q ∈ L} d(f₁,q))`.  The variant `#Bad ≤ L·max(1,2e)` without the floor
remains refuted (`L = 0`, `#Bad = 1`), which is exactly why the floor `1` is part of the
statement.

## D83.1 — what the charging theorem does and does not give

`Alphabet.exists_charging` and its corollaries are unconditional and code-generic (any linear
code over a module alphabet), but they bound `#Bad` **in terms of the nearby-codeword list**.
No bound on `|L(f₁,2e)|` is proved anywhere in this repository.  Inside the gap the list can be
large (`|L| = 76` in the recorded `RS[6,3]/F₇`, `e = 2` instance), and there the theorem is
weaker than the trivial `#Bad ≤ |F| − 1`.  In particular **no Johnson-radius, list-decoding
capacity or ordinary-RS capacity statement is proved or implied**, and no performance claim
follows.

## D83.2 — the charging map is canonical only after choices

The Lean statement asserts the *existence* of an injective charging map.  Its construction
fixes, by choice, one bad parameter `γ₀`, one agreement set and one codeword witness per bad
parameter.  Different choices give different maps; nothing is claimed about canonicity, about
the multiplicity of witnesses, or about the value of the maximal slope load (the experiments
observed at most 3, which is **not** a proved bound).

## D83.3 — refuted geometric invariants

The boundary/branching invariant `#Bad ≤ |⋃_{q ∈ L} supp(f₁ − q)|` and the radius invariant
`#Bad ≤ max(1, max_q d(f₁,q))` are refuted by explicit small instances recorded in
`GEOMETRIC_CHARGING_AUDIT.md`; the minimum-spanning-tree invariant was never strictly better
than the radial sum in the configurations tested.  These are negative results from exact
computation, not theorems: no claim is made that they fail for all parameters.

## D82.3 — scope of the circle factor-2 answer

The claim "the factor 2 is the dimension of the circle code" is supported by a *proved*
Singleton bound (`finrank_le_of_zeroBounded`, for a one-dimensional alphabet) together with an
*exhaustive but small* scan (circles of `F₅, F₇, F₁₁, F₁₃`, degree bounds `t' ≤ 2`).  The
statement "the circle code of degree bound `t'` has dimension exactly `2t'` on every admissible
domain" is not formalised; the scan exhibits it only for the domains listed.

## D84.1 — the capacity bound is still list-conditional

`ChargingCapacity.lean` improves the per-codeword factor from `2e` to `e + 1` (to `2` when every
nearby codeword is at distance `> 3e/2`), but the bound is still stated *in terms of a superset
`Q` of the nearby-codeword list*.  No bound on `|L(f₁,2e)|`, and none on the achieved-slope count
`A`, is proved anywhere in this repository.  Inside the gap the list can be large, and there the
new theorems remain weaker than the trivial `#Bad ≤ |F|`.  **No Johnson-radius, list-decoding
capacity or performance claim is proved or implied.**

## D84.2 — unrefuted but unproved list candidates

`#Bad ≤ max(1, 2·|L|)`, `#Bad ≤ max(1, |L| + e)` and `#Bad ≤ 1 + ∑_{q∈L}(d(f₁,q) − 1)` survived
all 34 514 gap instances of `analysis/list_geometry_frontier.py`, but no mechanism supports them
and they are **not** claimed.  They are recorded only as conjectures.

## D84.3 — negative results on the achieved-slope count

`A ≤ e + 1`, `A ≤ 2e`, `A ≤ w + 1` and `A ≤ n` are refuted by explicit instances recorded in
`LIST_GEOMETRY_FRONTIER.md` and `analysis/achieved_slopes_probe_output.txt`.  These are exact
counterexamples on the instances listed, not general theorems.

## D88.1 — the cyclotomic-coset gap is closed, but the complexity model is unchanged

The gap recorded at `factorCount_le_cover` (the maximal ideals of `F[C_n]` were only known to be
*at most* as many as the cyclotomic cosets) is now closed by
`FFT.Bilinear.factorCount_eq_frobClassCount`.  Two caveats remain.  First, the exact value
`3·2^{k−1} − 1` for length `2^k` is a **bilinear** complexity: it counts general multiplications
in a bilinear algorithm and says nothing about additions, memory traffic or wall-clock time, so it
is not a statement about any implementation being faster than another.  Second, the radix-2 family
is proved for `1 ≤ k ≤ 29` only, because the lower-bound route needs `2·2^k ≤ 2³¹ − 1`; the orbit
formula `t(2^k) = 2^{k−1} + 1` itself holds for `1 ≤ k ≤ 31`.

## D89.1 — scope of the redundancy kill

`natDegree_isGcd_shiftDet_famPlane_eq` shows the gcd degree is independent of the offset family
*on the sharp plane family*, and `card_badSetG_le_natDegree_of_isGcd` shows no gcd bound can ever
drop below `#Bad` for *any* family.  Neither statement says that redundancy is useless for every
`f`: where the determinants carry spurious roots the gcd does shrink, and
`badSetG_eq_empty_of_coprime` remains a genuine extreme case.  What is refuted is only the
existence of a *universal* law decreasing in the redundancy.  Also, `SynRecur` is a statement
about the length-`(2e+1)` syndrome *window* at a fixed offset, not about the linear complexity of
an infinite sequence; no claim is made beyond the available window.

## D90.1 — the converse of the key equation is open

`synRecur_of_errorType` gives "at most `e` errors ⟹ Hankel-singular".  The converse — that a
Hankel-singular challenge inside the available window must have a genuine `e`-error explanation —
is **not** proved here, and nothing in the project assumes it.  Consequently the class
`LowComplexity ∖ ErrorType` (the "spurious" challenges) is not known to be empty, and the
generic-phase equality `ErrorType = Bad` (`errorTypeSet_eq_badSetG_of_not_rigid`) does not by
itself turn the certified bound `#Bad ≤ deg D_{i₀}` into an equality.  Also, `RigidOffSmall` is a
statement about closeness of the whole family off a complement of an `e`-set; it is the same
degenerate branch that `SyndromeRigidityDichotomy.lean` handles, not a new hypothesis.

## D91.1 — (ND′) is now settled: it is **false**, and the four `threshold_rho_*_bchks` are vacuous

O41 left open whether the refined non-degeneracy hypothesis

    (ND′) ∀ f₀ f₁, (badSet k e f₀ f₁).Nonempty → ∀ Q, LineInterpolant … Q →
            ∃ x₀, discLine bY x₀ Q ≠ 0

is satisfiable.  It is **not**, at the parameter schedules of `threshold_rho_half_bchks` and
`threshold_rho_quarter_bchks`.  `NonDegeneracyExists.lean` proves:

* the interpolation conditions are multiplicative, so `Q₀²` is an interpolant at the doubled
  schedule (`GS.hasMultAt_mul`, `GS.wdegLt_mul`, `GS.zdegLe_mul`, `LineInterpolant.sq`);
* the line discriminant of a square vanishes at *every* point (`discLine_eq_zero_of_isSq`);
* lines with a bad point exist at every rate and radius in range
  (`exists_badSet_nonempty`, the spike `f₀ = δ_{x₀}`, `f₁ = −f₀`, `γ = 1`), so the
  `badSet`-nonempty guard does not save (ND′);
* the halved schedule still meets the Guruswami–Sudan counting condition at both prize
  parameter sets, using the sharpened count `2k·#monIdx(k,L) ≥ L² + kL`
  (`GS.card_monIdx_ge'`, `count_of_clean'`).

Hence `nd_forall_false`, and its two instances `nd_forall_false_rho_half`,
`nd_forall_false_rho_quarter`.  **Consequence:** `epsMCAmax_le_bchks_nat`,
`epsMCAmax_le_bchks_disc`, `epsMCAmax_le_bchks_linear`, `exists_const_epsMCAmax_le_bchks`,
`epsMCAmax_le_of_schedule`, `threshold_rho_{half,quarter,eighth,sixteenth}_bchks` and
`epsMCAmax_le_bchksRHS_rho_{half,quarter}` are vacuously true at those schedules and certify
nothing.  Nothing has been deleted; the statements stand and are correct as stated, but they
must not be read as thresholds.

The repair is the existential form, which the square construction does **not** refute:

    (ND∃) ∀ f₀ f₁, (badSet k e f₀ f₁).Nonempty →
            ∃ Q x₀, LineInterpolant … Q ∧ discLine bY x₀ Q ≠ 0.

`epsMCAmax_le_disc_of_bad` already carries it, and `epsMCAmax_le_of_schedule_exists`,
`threshold_rho_half_bchks_exists`, `threshold_rho_quarter_bchks_exists` re-derive the two prize
certificates under it with the *same* constants (`#Bad ≤ 2³²`, `ε_mca ≤ 2⁻¹²⁸` for
`|F| ≥ 2¹⁶⁰`).  Whether (ND∃) holds is **open**; it is now the single remaining gap on the
Johnson-radius route.  This supersedes the "not settled" verdict of O41 and the wording of
O40 and O46 about (ND′).

## D91.2 — the unique-decoding barrier is about the mechanism, not about MCA

`ForcingBarrier.lean` proves that the canonical-pair extraction underlying
`card_badSet_le_unconditional` (and every other unique-decoding-regime bound here) has a unique
output iff `k + 2e ≤ |D|`, and strictly beyond has *no* output on the guaranteed intersection
(`forcing_unique_at_frontier`, `forcing_not_unique_beyond_frontier`,
`exists_two_interpolants_of_card_lt`, `forcing_guaranteed_size_ge_iff`).

This is **not** a statement that MCA fails past `(1−ρ)/2` — it does not, up to the Johnson
radius — and it is **not** a lower bound on `#Bad`.  It only says that the determinant /
locator / subresultant formalism cannot be pushed past `k + 2e ≤ |D|` by sharpening estimates,
because past that point the object it extracts does not exist.  No claim of optimality of the
constant `(k+1)e + 1` is made, and no claim that some *other* mechanism cannot cross the
frontier.

### 8.9 Additions to the FFT layer (this round)

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P55 | **Radix 4 in the twiddle-count model**: classification of the free twiddles of all four branches, `3m − 4` multiplications per radix-4 level against `4m − 4` for the two radix-2 levels it replaces, hence radix 4 is strictly cheaper than radix 2 from `k ≥ 4`, and split radix is never worse than radix 4 | `radix4_free_odd_branch`, `radix4_free_even_branch`, `radix4Cost_lt_radix2Cost`, `splitRadixCost_le_radix4Cost`, `radix4_cost_table` | `RequestProject/Radix4.lean` |
| P56 | **Bluestein's chirp transform**: the length-`n` DFT is one cyclic convolution of any length `L ≥ 2n − 1`, with no arithmetic hypothesis on `n`; at odd `n` the chirp comes from `⟨ζ⟩`; over `M31` the length-31 transform is a single length-63 convolution whose chirp constants are all powers of two | `dft_eq_chirp_conv`, `sq_root_of_odd`, `dft_eq_chirp_conv_odd`, `M31.dft31_eq_chirp_conv63`, `M31.chirpKer63_is_rotation` | `RequestProject/Bluestein.lean` |

Both rows are audited in `RequestProject/Main.lean` and depend only on `propext`,
`Classical.choice`, `Quot.sound`. No `axiom`, no `sorry`, no `admit`.  The cost statements of
P55 are relative to the model defined in `SplitRadix.lean`; P56 contains no cost statement and
no benchmark was run.

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P57 | **Radix 8 in the same model**, with the divisibility criterion `(ζ^e)^4 = 1 ↔ N ∣ e` for `ζ` primitive of order `4N`, the free twiddles of all eight branches (`7m − 8` per level plus `m` eight-point butterflies at `radix2Cost 3 = 2`), and the verdict `radix4Cost ≤ radix8Cost ≤ radix2Cost` | `four_pow_eq_one_iff`, `radix8_free_odd_branch`, `radix8_free_four_branch`, `radix8Cost_le_radix2Cost`, `radix4Cost_le_radix8Cost`, `radix8_cost_table` | `RequestProject/Radix8.lean` |

P57 is audited in `RequestProject/Main.lean` on the same axioms.  Its cost statements are
relative to the same model, which charges one unit for every multiplication by a constant
outside `μ₄`; that is why the verdict is a statement about the model and not about any
implementation.

| # | Statement | Lean name | File |
| --- | --- | --- | --- |
| P58 | **`𝔽_{p²}` radix-2 NTT versus the circle FFT** in base-field multiplications: same butterfly count, extension multiplication exactly three base multiplications, hence a factor 3 (and 3/2 against packing) in favour of the circle route | `extRadix2_correct`, `extBaseMuls_eq_three_mul`, `circle_lt_ext_baseMuls`, `circle_lt_ext_packed`, `baseMuls_table` | `RequestProject/ExtensionVsCircle.lean` |
| P59 | **The isotypic decomposition as one natural isomorphism**: the diagonalisation functor `X ↦ ⨁_{j<n} ker (ρ(g) − ζ^j)` and the natural isomorphism `diag ≅ forget` on `Rep K C_n`, together with the two computation rules identifying it with the DFT (sum of components forwards, Fourier modes `(1/n) ∑_k ζ^{−jk} ρ(g)^k v` backwards) and the `M31` instance at `n = 31`, `ζ = 2` | `FFT.diagFunctor`, `FFT.diagNatIso`, `FFT.diagNatIso_hom_apply`, `FFT.dftModes`, `FFT.diagNatIso_inv_app`, `FFT.M31.diagNatIso31` | `RequestProject/IsotypicNatIso.lean` |
| P60 | **The free (power-of-two) twiddles of the circle FFT over `M31`, exactly**: `p^{2^k} = 1 ↔ π^k(p.x) = 1` for the doubling map `π(x) = 2x² − 1`; hence for `m + 2 ≤ 27` every circle-FFT twiddle lying in `⟨2⟩` is `1` or `2¹⁵ = 1/√2`, both bounds sharp, with the complete count table `1, 2, 3, 5, 8, 16` up to the whole circle group `2³¹` | `FFT.Circle.pow_two_pow_eq_one_iff`, `FFT.Circle.MersenneFree.circleTw_free`, `…x_free_of_pow_eq_one`, `…y_free_of_pow_eq_one`, `…pt45_order`, `…pt27_order`, `…chebD_two_pow_iff`, `…freeLevel_card` | `RequestProject/CircleFreeTwiddles.lean` |

P58 is audited in `RequestProject/Main.lean` on the same axioms; it counts multiplications
only (no additions, no memory traffic) and no benchmark was run.

## D92.1 — (DICH) is **false**, and (ND∃) was stronger than the chain consumed

`ND_EXISTS_MISSION_REPORT.md` left the dichotomy

> **(DICH)** either the line is near the codeword-line variety — and then its bad set is
> small directly — or it is far, and then some admissible interpolant is separable in `Y`

as the only surviving proposal after (ND∃), (SF∃), (CO∃), (GCD-SEP∃) were refuted.  The far
half is now refuted: `dichFar_fails` (`CurveLineDegeneracy.lean`) exhibits, at both prize
schedules, a line which is far from the codeword-line variety (any pair of codewords agrees
with it on at most `K < k + e` positions), has a nonempty bad set, and has **no** separable
admissible interpolant — because *every* admissible interpolant is divisible by
`(Y − (a + Z·b))²`.  So the obstruction to separability is not proximity to a codeword line
but proximity to a curve of degree `≤ K*`, one degree class above the code.

Two further corrections to earlier wording:

* **(ND∃) is not necessary.**  The bottleneck trace in `JOHNSON_MIN_J_REPORT.md` shows the
  chain consumes only `discLine b x₀ Q ≠ 0` at one *free* evaluation point — not full
  `Y`-degree, not `gcd(Q, ∂_Y Q) = 1`, not root distinctness.  The full-`Y`-degree hypothesis
  was already flexible via `epsMCAmax_le_disc_of_bad_flex`.
* **But no weakening inside that paradigm can work.**  `eval_discLine_eq_zero_of_isBad`
  destructures `IsBad` and *discards* the `¬ LineCloseOn` conjunct, so the chain bounds the
  close set, not the bad set; on the spike lines the close set is all of `F`.  Any repair
  must consume `¬ LineCloseOn`, e.g. by the family-of-annihilators counting step
  (`card_badSet_le_of_annihilator_family`), whose budget cost is `2^40.34` — affordable at
  the actual KoalaBear sextic field (`B_max = 2^57.93`) but **not** under the `|F| ≥ 2^160`
  hypothesis of the repository's certificate statements (`B_max = 2^32`).

The refuted lines are, however, harmless: `curveLine_card_badSet_le_one` shows a curve line
with `K + e < |D|` has at most one bad challenge, and
`degeneracy_threshold_lt_witness_size` records that the forced-degeneracy threshold satisfies
`K* < t ⟺ k|D| < t² ⟺ t > √(k|D|)`, i.e. exactly the Johnson condition.  No Johnson-radius
theorem follows; the remaining question is whether a shared square factor can be forced above
`K*`.

## D93.1 — the `δ > 1/4` certificate is conditional, and the gap window is the only gap

`johnson_rho_half_delta_quarter` certifies `ε_mca ≤ 2⁻¹²⁸` at `ρ = 1/2` and
`δ = 262145/2²⁰ > 1/4`, but **only under the hypothesis `GapBound`**, which is a `def` in
`JohnsonStructuralDichotomy.lean` and is *not* proved.  The unconditional certified radius
remains `δ = 0.177124…` (`nearFar_rho_half`).  Nothing in §109 raises it.

The reduction is honest in both directions: outside the window `c+1 ≤ |T| < k+e` the
corresponding statement is a theorem (`unexplainedBadSet_eq_empty_of_large_pair` above the
window, `johnson_escape_or_structure` below it), so `GapBound` is exactly what is missing —
but it is missing, and at `ρ = 1/2` any `δ > 1/4` is strictly past unique decoding
(`|D| − 2e = k − 2` at the schedule used), where every elementary argument tried in this
session fails by a margin of two positions.  The next route (key-equation / Hankel pencil,
degree-one annihilators) is recorded in `JOHNSON_STRUCTURAL_DICHOTOMY_REPORT.md`; it is a
plan, not a result.

## D112.1 — `#Bad ≤ e+1` needs `κ ≥ 3e`; core/fibre decompositions of the bad set are all false

Any statement of the form "an MCA line has at most `e + 1` bad challenges in the
unique-decoding regime" is **false**.  `FoldPencil.lean` exhibits, for every radius `e` and
every rate on the band `2e ≤ κ ≤ 3e − 1`, a line with `|D|/e − 2` bad challenges, and for
`e = 1`, `κ = 2` a line with `|D| − 2` bad challenges on *every* evaluation domain.  The
correct hypothesis is the one `card_badSet_le_succ_radius` already carries, `3e < κ + 1`,
and it is sharp.

The mission's core/fibre programme is refuted in all four of its forms (details and smallest
exact counterexamples in `IRREGULAR_CORE_FIBRE_REPORT.md`): in the extremal band families the
error sets of distinct bad challenges are pairwise **disjoint**, so there is no literal common
core (H1) and no robust core (H2); the agreeing codewords span a space of dimension
`#Bad − 1 = Θ(|D|/e)`, so they lie in no bounded-dimensional container (H3); and every fibre
of `γ ↦ p_γ` is a singleton, so the component decomposition `#Bad ≤ Σ_ξ fibreCap(ξ)` is
tautological (H4).  The per-component cap itself is true and is formalised
(`CoreCharge.card_le_succ_of_lt_core`), but the number of components is unbounded.

What survives as the organising invariant is a **fold (quotient) of the domain**: the bad
challenges are indexed by the sectors of `D ↠ D/μ_e` (multiplicative model), and `#Bad` is
governed by the number of sectors, not by the radius.  Sunflower / VC machinery is
quantitatively useless here: the extremal window family is already a `Δ`-system with empty
core and only `|D|/e` members.

## D113.1 — "`ε_mca ≤ poly(|D|)/|F|` up to capacity" is false; the binomial bounds are sharp

Grand MCA in its quantitative form — a bound `#Bad ≤ poly(|D|)`, equivalently
`ε_mca ≤ poly(|D|)/|F|`, valid at every radius `δ < 1 − ρ` — is **false**.  At capacity gap
`c = |D| − k − e = 1` the maximum of `#Bad` over all Reed–Solomon MCA lines is exactly
`C(|D|, e)` (`card_badSet_le_choose_succ_dim` and `card_badSet_eq_choose_gapOne`), attained by
the power pencil `f₀ = x^{k+1}`, `f₁ = x^k` on any domain with distinct `(k+1)`-subset sums —
concretely `{1, 2, …, 2^{m−1}} ⊆ ZMod p` with `2^m < p`.  With `|D| = n = 2(k+1)` this reads
`2^n ≤ n · #Bad`.

Consequences for the repository's bookkeeping:

* The window-free binomial rows (`card_badSet_le_circuit`, `card_badSet_le_choose_radius`) are
  **not** improvable to polynomial bounds in general: they are attained at `c = 1`.  Their
  status changes from "crude fallback" to "sharp at the capacity boundary layer".
* Any future row asserting a polynomial bound at radii beyond Johnson must carry a hypothesis
  bounding the capacity gap away from zero, at least `c = Ω(|D| / log|D|)`; the general
  obstruction is `#Bad ≥ C(|D|/c, k/c + 1)` (`card_badSet_ge_blocks`,
  `exists_capacityGap_counterexample`), i.e. `exp(Ω(1/η))` with `η = 1 − ρ − δ`.
* Nothing in the Johnson regime, in unique decoding, or at a constant gap `η` is contradicted;
  in particular the previously recorded empirical cap `#Bad ≤ max(e+1, |D|/(κ−2e+1))` lives in
  `2e ≤ κ`, whereas the counterexamples above have `κ = e + c` with `c ≪ e`.

## D114.1 — the conjectural gap-layer law `max #Bad ≍ poly(n) + exp(Θ(1/η))` is false

After §113 the natural reading of the evidence was that `#Bad` is polynomial outside the
capacity boundary layer `c = O(|D|/log|D|)`, with an `exp(Θ(1/η))` spike inside it.  The
subspace pencil (§114, `exists_superpolynomial_badSet_of_small_relative_gap`) refutes this:
for every polynomial degree `d` and every `M`, there are parameter points with relative gap
`η ≤ 1/M` and `#Bad > |D|^d`.  The true order supplied by the construction is
`#Bad ≳ n^{log_p(1/η)}`, superpolynomial at *every* vanishing `η`.

Bookkeeping consequences:

* Any row asserting a polynomial bound on `#Bad` beyond Johnson must assume `η = Ω(1)`
  outright; the weaker hypothesis `c = Ω(|D|/log|D|)` recorded in D113.1 is **not** sufficient
  and is hereby superseded.
* The remaining open case is exactly constant `η`.  D113.1's remark that "nothing at a constant
  gap `η` is contradicted" still stands, and is now known to be the sharp boundary rather than
  an artefact of the earlier construction.
* Not a contradiction of any formalised statement in the repository: no Lean theorem claimed a
  polynomial bound in the range `η = o(1)`, `c = ω(|D|/log|D|)`.  The affected claims were
  informal expectations recorded in prose.

## D114.2 — the reading of the subspace pencil is corrected: existence, not "every vanishing gap"

`SUBSPACE_PENCIL_REPORT.md` (title, §§0 and 3), the docstring of
`exists_superpolynomial_badSet_of_small_relative_gap`, §114 of `RESULTS.md` and D114.1 above
described the subspace pencil as showing that `#Bad` is superpolynomial *at every* vanishing
relative capacity gap, with "true order `#Bad ≳ n^{log_p(1/η)}`".

**That reading is not justified**, and for this family it is false.  The Lean theorem is an
existence statement — for each `(d, M)` *some* parameter point has `η ≤ 1/M` and `#Bad > n^d`,
with the point depending on `d`.  Certified in
`RequestProject/Root/CodingTheory/SubspacePencilAudit.lean` (see §116 of `RESULTS.md`):

* `subspacePencil_superpoly_forces_gap`: beating `n^d` forces `m − ℓ > d`, i.e. `η < p^{−d}`;
* `subspacePencil_bound_le_pow_card`: the guarantee never exceeds `n^{m−ℓ} ≈ n^{log_p(1/η)}`,
  hence is polynomial at every fixed `η`;
* `subspacePencil_vanishing_gap_linear_bound`: at `ℓ = 1` the gap `η ≤ p^{1−m}` vanishes while
  the guarantee is only `p^{m−1} < n`.  The exponent is `ℓ(m−ℓ)/m`, not a function of `η`;
* `subspacePencil_gap_eq_pred_mul`: `c = (p−1)(k−1)`, so the family's vanishing gap is tied to
  a vanishing rate (`η ≈ (p−1)ρ`, `δ → 1`); constant-rate small-gap parameters are untouched.

Bookkeeping consequences:

* D114.1 stands where it uses only the existence form: the gap-layer law
  `poly(n) + exp(Θ(1/η))` is still refuted.  Its sentence "the true order supplied by the
  construction is `#Bad ≳ n^{log_p(1/η)}`, superpolynomial at *every* vanishing `η`" is
  **superseded** by this row.
* No Lean statement was wrong; the affected claims were in prose and in docstrings, and have
  been corrected in place.
* The open case remains constant `η`, and by §117 of `RESULTS.md` it is *equivalent* to the
  constant-gap proximity-gap problem for Reed–Solomon lines.
