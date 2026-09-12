# FFT over the Mersenne field `M31 = 𝔽_{2³¹−1}` — formalised results

All statements below are **proved in Lean 4 + Mathlib**, with no `sorry`, no added
axioms and no `native_decide`. `RequestProject/Main.lean` prints the axiom audit of the
headline theorems (only `propext`, `Classical.choice`, `Quot.sound` occur).

Build: `lake build`.

## 1. The field and its structure (`M31Basic.lean`, `FiniteFieldRoots.lean`)

| Result | Lean name |
| --- | --- |
| `2³¹ − 1` is prime | `FFT.mersenne31_prime` |
| `𝔽_q` has a primitive `n`-th root of unity **iff** `n ∣ q − 1` | `FFT.exists_primitiveRoot_iff` |
| `\|M31\| − 1 = 2 · 3² · 7 · 11 · 31 · 151 · 331` | `FFT.M31.card_sub_one_factorization` |
| 2-adic capacity of `M31` is exactly 1 | `FFT.M31.two_adic_capacity` |
| **No primitive `2^k`-th root of unity in `M31` for `k ≥ 2`** | `FFT.M31.no_primitiveRoot_two_pow` |
| `(hi·2³¹ + lo) mod p = (hi + lo) mod p` | `FFT.mersenne_fold_mod` |
| **Multiplication by `2^k` mod `2^n−1` is a bit rotation, already reduced** | `FFT.mul_two_pow_mod_mersenne` |

The obstruction result is the formal reason why a radix-2 NTT cannot run over `M31`
itself. Its positive counterpart (`M31Ext.lean`):

| Result | Lean name |
| --- | --- |
| `\|𝔽_{p²}\| − 1 = 2³² · 1073741823` | `FFT.M31sq.card_sub_one` |
| `𝔽_{p²}` has primitive `2^k`-th roots for all `k ≤ 32` | `FFT.M31sq.exists_primitiveRoot_two_pow` |
| `𝔽_{p²}` has primitive `31·2^k`-th roots for all `k ≤ 32` | `FFT.M31sq.exists_primitiveRoot_31_mul_two_pow` |
| base field caps at length 2, extension at `2³²` | `FFT.M31sq.base_field_cap_vs_extension` |

## 2. The DFT (`DFT.lean`)

| Result | Lean name |
| --- | --- |
| character orthogonality `∑_{j<n} ζ^{mj} = n·[n∣m]` | `FFT.sum_pow_mul` |
| inversion formula `DFT_{ζ⁻¹} ∘ DFT_ζ = n·id` | `FFT.dft_dft_inv` |
| DFT matrix = Vandermonde of `ζ^i`, determinant formula | `FFT.det_dftMatrix` |
| invertibility for primitive `ζ` | `FFT.det_dftMatrix_ne_zero`, `FFT.isUnit_dftMatrix` |
| `W(ζ)·W(ζ⁻¹) = n·I` | `FFT.dftMatrix_mul_inv` |
| `W(ζ)² = n·R` (`R` = reflection `i ↦ −i` of `ℤ/n`) | `FFT.dftMatrix_sq` |
| `det W(ζ)² = n^n · det R` | `FFT.det_dftMatrix_sq` |
| the `K₁(F) ≅ Fˣ` class of the DFT (= its determinant) and its square | `FFT.dftK1Class`, `FFT.dftK1Class_sq` |
| the DFT diagonalises the cyclic shift (regular representation of `C_n`) | `FFT.dft_shift`, `FFT.dft_intertwines_shift` |

## 3. Algorithms

### Radix-2 Cooley–Tukey (`CooleyTukey.lean`)

* `FFT.fftRec` — the decimation-in-time recursion; `FFT.fftRec_eq_dft` proves it equals
  the DFT assuming only `ζ^(2^k) = 1` (primitivity is needed only for inversion,
  `FFT.fftRec_inversion`).
* Exact operation counts, with closed forms: `FFT.fftMuls_eq`, `FFT.fftAdds_eq`
  (`k·2^k` each), and for the standard `ζ^{j+2^k} = −ζ^j` butterfly
  `FFT.fftMulsOpt_eq` (`2·M_opt(k) = k·2^k`, i.e. exactly half), plus
  `FFT.fftMulsOpt_lt_fftMuls` and `FFT.fftMulsOpt_lt_direct` (`< n²`).

### Bit reversal (`BitReversal.lean`)

`FFT.bitrev_lt`, `FFT.bitrev_bitrev` (**involution**), `FFT.bitrevPerm` /
`FFT.bitrevPerm_symm` — the permutation of `Fin (2^k)` is its own inverse.

### The multiplication-free length-31 transform (`M31FFT.lean`, `OpCount.lean`)

The key arithmetic fact is `orderOf (2 : M31) = 31` (`FFT.M31.orderOf_two`), so every
twiddle factor of the 31-point DFT over `M31` is a power of two, i.e. a rotation.

* `FFT.rot31` / `FFT.rot31_cast` — the rotation kernel implements multiplication by `2^s`;
* `FFT.dft31` / `FFT.dft31_correct` — a length-31 DFT written with shifts, masks and
  additions only, proved to compute the mathematical DFT;
* `FFT.dft31_no_overflow` — the accumulator stays below `2³⁷`, so 64-bit accumulation
  with a single final reduction is safe;
* `FFT.idft31` / `FFT.idft31_correct` / `FFT.idft31_dft31` — the inverse transform is
  multiplication-free as well (`2⁻¹ = 2³⁰`, `FFT.M31.inv_two`), and the round trip
  forward-then-inverse multiplies the data by `31`;
* `OpCount.lean` makes "no multiplications" a **theorem about the program**, not a
  comment: a small straight-line-program calculus (`FFT.Expr`) with evaluation semantics
  and operation counters gives
  `FFT.eval_dft31Expr` (the program computes the DFT),
  `FFT.mulCount_dft31Expr = 0`, `FFT.addCount_dft31Expr = 30`,
  `FFT.rotCount_dft31Expr = 31`, and the aggregate `FFT.dft31_program_cost`
  (`0` multiplications, `930` additions, `961` rotations for all 31 outputs).

### Rader and mixed radix (`M31FFT.lean`, `MixedRadix.lean`)

* `FFT.rader31` — Rader's identity for the prime length 31: re-indexing along the powers
  of the primitive root `3 mod 31` turns the length-31 DFT into a cyclic correlation of
  length 30; `FFT.rader31_M31` is the `M31` instance, where the correlation kernel
  consists of powers of two (rotations).
* `FFT.dft_mixed_radix` — the general Cooley–Tukey factorisation
  `DFT_{n₁n₂}(j) = ∑_{r<n₂} ζ^{rj}·DFT_{n₁}(ζ^{n₂})`, valid for any `ζ`.
* `FFT.dft31_hybrid` — the hybrid `31·m` decomposition over `M31`, whose inner
  transforms are exactly the multiplication-free 31-point kernels.
* Micro-kernels: `FFT.dft2_explicit` (length 2: two additions, no multiplication) and
  `FFT.dft4_explicit` (length 4: a single multiplication by `ζ`, `ζ² = −1`).

### The convolution theorem (`Convolution.lean`, `RaderConvolution.lean`)

* `FFT.cyclicConv` — cyclic convolution `(a ⊛ b)_k = ∑_{i<n} a_i · b_{(k−i) mod n}`.
* `FFT.dft_cyclicConv` — **convolution theorem**: for any `ζ` with `ζⁿ = 1`,
  `DFT(a ⊛ b)_j = DFT(a)_j · DFT(b)_j`. In other words the DFT is the coordinate form of
  the algebra isomorphism `F[ℤ/n] ≅ Fⁿ`.
* `FFT.dft_inv_pointwise_mul` — the algorithmic converse: for `ζ` primitive of order `n`,
  `DFT_{ζ⁻¹}(j ↦ DFT(a)_j·DFT(b)_j)_k = n·(a ⊛ b)_k`, i.e. convolution costs three
  transforms plus `n` pointwise products.
* `FFT.cyclicConv_reverse` — reversing one argument converts a cyclic correlation into a
  cyclic convolution, the form in which Rader's algorithm delivers its output.
* `FFT.rader31_conv` / `FFT.rader31_conv_M31` — the length-31 DFT equals `a₀` plus a
  genuine length-30 cyclic convolution of the permuted data with the kernel `m ↦ ζ^{3^m}`;
  over `M31` that kernel consists of powers of two, i.e. bit rotations.
* `FFT.M31.no_primitiveRoot_thirty` — a second negative structural fact: `5 ∤ p − 1`, so
  `M31` has **no** primitive 30-th root of unity. Hence the length-30 convolution coming
  out of Rader's reduction cannot itself be evaluated by length-30 transforms over `M31`;
  it must be done by another scheme (extension field, or a direct / short-convolution
  algorithm). This is exactly the kind of constraint an implementation has to respect.

### The circle group: radix-2 depth 31 inside the base field (`CircleGroup.lean`)

`M31` has no primitive `2^k`-th root of unity for `k ≥ 2`, but the circle group
`C(F) = {(x,y) : x² + y² = 1}` with `(x,y)·(u,v) = (xu − yv, xv + yu)` does have 2-power
structure over `M31`:

| Result | Lean name |
| --- | --- |
| `C(F)` is a commutative group | `FFT.Circle.instCommGroup` |
| `\|C(F)\| = \|F\| + 1` when `−1` is not a square and `char F ≠ 2` (stereographic projection) | `FFT.Circle.card_circle` |
| `\|C(M31)\| = 2³¹` | `FFT.Circle.card_circle_M31` |
| the explicit point `(1717986917, 1288490189)` has order exactly `2³¹` | `FFT.Circle.orderOf_gen` |
| `C(M31)` is cyclic | `FFT.Circle.isCyclic_circle_M31` |
| elements of order `2^k` exist for every `k ≤ 31` | `FFT.Circle.exists_orderOf_two_pow` |

The order of the generator is certified by kernel computation of 31 successive squarings
(`FFT.Circle.sqIter_eq_pow` reduces `g^(2^n)` to repeated squaring).

### Specification ≡ implementation (`Bridge.lean`)

`FFT.mulVec_dftMatrix_eq_dft` and `FFT.fftRec_eq_mulVec` identify the butterfly
implementation with the matrix specification; `FFT.dftEquiv` packages the DFT as a linear
automorphism. This equality is what the Verus contracts refer to.

## 4. Machine-word layer (`MachineM31.lean`)

The bit → field path, in the *quasi-canonical* (redundant) representation: a word
`a : UInt32` denotes `toF a = a mod p`, and the invariant is `QC a : a.toNat ≤ 2³¹−1`
(so zero has two representations, `0` and `p`; this is what makes the kernels
branch-free).

| Result | Lean name |
| --- | --- |
| exact word semantics of the kernels | `FFT.Machine.add_toNat`, `sub_toNat`, `neg_toNat`, `mulLo_toNat`, `mulHi_toNat` |
| the kernels compute the field operations | `FFT.Machine.toF_add`, `toF_sub`, `toF_neg`, **`toF_mul`** |
| the invariant is preserved | `FFT.Machine.QC_add`, `QC_sub`, `QC_neg`, `QC_mul` |
| branch-free mask variants coincide with them | `FFT.Machine.addMask_eq_add`, `subMask_eq_sub` |
| canonicalisation and injectivity on canonical words | `FFT.Machine.canon_lt`, `toF_canon`, `toF_injOn_canonical` |
| 64-bit Mersenne fold | `FFT.Machine.toF64_fold`, `toF64_add` |
| **lazy reduction**: after `k` additive levels values stay `< B·2^k` | `FFT.Machine.lazy_levels_bound` |
| with `B = 2³¹`, `K ≤ 32` levels never overflow a `u64` | `FFT.Machine.lazy_levels_no_overflow` |

`FFT.Machine.mul` is the 32×32→64 multiply followed by one Mersenne fold `hi + lo`
(`mulHi`/`mulLo` are a shift and a mask), and `toF_mul` is the bit-level correctness
statement requested in Phase A.

### Bits → field → transform (`MachineButterfly.lean`)

`FFT.Machine.mieval` is the evaluation recursion of the butterfly tower executed with the
`UInt32` kernels. `FFT.Machine.QC_mieval` shows the quasi-canonical invariant holds
throughout (no intermediate value leaves the legal range) and `FFT.Machine.toF_mieval`
shows the word-level computation equals the field computation; composed with the circle
instance, `FFT.Machine.toF_mieval_circle` states that the word-level program computes the
inverse circle FFT.

## 5. Circle FFT (`ButterflyTree.lean`, `CircleFFT.lean`)

`M31` has 2-adic capacity 1, but its circle group `C(M31) = {(x,y) : x²+y² = 1}` is
cyclic of order `2³¹`, so the radix-2 butterfly schedule runs on a domain of circle
points. The development first isolates the *generic* structure — a twiddle tower
`T k : ℕ → F` with the antisymmetry `T k (i + 2^k) = −T k i` and non-vanishing
(`FFT.Tree.Good`) — and proves everything there:

| Result | Lean name |
| --- | --- |
| interpolation inverts evaluation, and conversely | `FFT.Tree.fwd_ieval`, `FFT.Tree.ieval_fwd` |
| semantics: evaluation of the twiddle-monomial basis | `FFT.Tree.ieval_eq_sum`, `FFT.Tree.basis` |
| exact costs `2·M(n) = n·2^n`, `A(n) = n·2^n` | `FFT.Tree.imulCount_eq`, `FFT.Tree.iaddCount_eq` |

The circle instance: for a point `q` of order `2^(m+2)` the domain is the twin coset
`{q^(4i+1)} ∪ {q^(−(4i+1))}` of size `2^(m+1)` (`FFT.Circle.cpt`, `cpt_add` — the second
half is the `J`-image of the first), the top-level twiddle is the `y`-coordinate and the
lower levels are the `x`-coordinates produced by the squaring map `π(x) = 2x²−1`
(`FFT.Circle.circleTw`, `circleTw_squaring`), and the tower is admissible
(`FFT.Circle.circleTw_good`).

| Result | Lean name |
| --- | --- |
| `cfft` and `icfft` are mutually inverse | `FFT.Circle.cfft_icfft`, `FFT.Circle.icfft_cfft` |
| over `M31`, for every domain size `2^n`, `n ≤ 30` | **`FFT.Circle.M31.cfft_correct`** |
| the inverse transform is the circle-code low-degree extension | `FFT.Circle.icfft_eq_sum` |
| exact cost: `n·2^(n−1)` multiplications, `n·2^n` additions | `FFT.Circle.cfft_cost` |

## 6. Free twiddles over Mersenne fields (`FreeTwiddles.lean`)

Multiplication by an element of `⟨2⟩ ⊆ 𝔽_{2ⁿ−1}ˣ` is a rotation, hence free in the
straight-line-program model. `FFT.Mersenne.mulCount_sumProg_eq` computes the number of
general multiplications of the natural DFT program as *exactly* the number of twiddles
outside `⟨2⟩`; `FFT.Mersenne.dft_mul_free` shows that for `m ∣ ord(2)` and
`ζ = 2^(n/m)` this number is zero, and `FFT.Mersenne.M31.mul_free_lengths` specialises:
over the base field `M31` the multiplication-free lengths are exactly `1` and `31`.

## 7. Prime-factor (Good–Thomas) composition (`GoodThomas.lean`)

For `gcd(n₁, n₂) = 1`, indexing inputs by `i = (i₁e₁ + i₂e₂) mod n` and outputs by
`j = (j₁n₂ + j₂n₁) mod n` (CRT idempotents `e₁, e₂`, `FFT.exists_crt_idempotents`) makes
the length-`n₁n₂` DFT a *pure* tensor product of its two sub-transforms — **no twiddle
factors at all** (`FFT.dft_pfa`, `FFT.dft_pfa_nested`), in contrast with the mixed-radix
factorisation `FFT.dft_mixed_radix`, which pays a twiddle per index pair.

Over `M31` with `n = 31·m`, `gcd(31, m) = 1`, the outer root is `ζ^m = 2`, so the outer
stage is the rotation kernel: the combination step is multiplication-free
(`FFT.pfa31_mulCount` = 0, `FFT.pfa31_rotCount` = 31, `FFT.pfa31_addCount` = 30) and
computes the correct output (`FFT.eval_pfa31`). Costs here are counted in the explicit
expression model of `OpCount.lean`, per output tree (no sharing between outputs).

## 7b. Split radix (`SplitRadix.lean`)

One decimation-in-frequency identity covers every radix (`FFT.dft_dif`): for
`ζ^(d·m) = 1`,

`DFT_{d·m}(a)(d·j + r) = DFT_m(ζ^d)( s ↦ ζ^{r·s}·∑_{t<d} a(m·t+s)·ζ^{m·t·r} )(j)`,

whose `d = 2` cases are the radix-2 butterfly (`FFT.dft_dif_two_even` — *no* twiddles —
and `FFT.dft_dif_two_odd`) and whose `d = 4`, `r ∈ {1,3}` cases are the odd quarters of a
split-radix step (`FFT.dft_split_radix_odd`).

Which twiddles are free is settled exactly: for primitive `ζ` of order `4m`, the radix-2
twiddles `ζ^i` (`i < 2m`) lie in `μ₄ = {±1, ±I}` precisely for `i = 0, m`
(`FFT.radix2_free_twiddles`), and the split-radix twiddles `ζ^{r·i}` (`i < m`, `r`
coprime to `m`) only for `i = 0` (`FFT.split_radix_free_twiddles`). The resulting counts

`R(k+1) = 2R(k) + 2^k − 2`,  `S(k+1) = S(k) + 2S(k−1) + 2^k − 2`

satisfy `R(k+3) = k·2^{k+2} + 2` (`FFT.radix2Cost_closed`) and

**`FFT.splitRadixCost_lt_radix2Cost`: `S(k) < R(k)` for every `k ≥ 4`** — a proved
multiplication saving, in the model where multiplications by fourth roots of unity are
free (they agree for `k ≤ 3`; `FFT.cost_table` lists `R = 10, 34, 98, 258, 642` against
`S = 8, 26, 72, 186, 456` for `k = 4 … 8`).

`R` and `S` are definitions of the twiddle counts of the two recursions in that model,
justified by the identities above but not extracted from a formal program object.

## 8. A lower bound (`SLPLowerBound.lean`)

All the results above are *upper* bounds. This file adds the first lower bound, in an
explicit register-machine straight-line-program model where additions, subtractions and
multiplications by constants are free and only general multiplications are counted
(`FFT.SLP.mulCount`):

* `FFT.SLP.no_mul_isAff` — a program with no general multiplication computes an affine
  function of the inputs;
* `FFT.SLP.mul_lower_bound_one`, `FFT.SLP.cyclicConv2_lower_bound` — computing both
  outputs of the length-2 cyclic convolution needs **at least 2** general
  multiplications;
* `FFT.SLP.cyclicConv2_prog` with `cyclicConv2_prog_cost = 2` and
  `cyclicConv2_prog_correct` — an explicit program attaining it;
* **`FFT.SLP.cyclicConv2_optimal`** — the multiplicative complexity of the length-2
  cyclic convolution is exactly 2, matching Winograd's `2n − t(n)` with `n = 2`,
  `t(2) = 2` (the factorisation `x² − 1 = (x−1)(x+1)` over a field of characteristic
  ≠ 2).

The general question — an `Ω(n log n)` lower bound for arithmetic circuits computing the
DFT — is **open**; nothing in this development bears on it, and no claim is made.

### Karatsuba in the quadratic extension (`Karatsuba.lean`)

`𝔽_{p²} = 𝔽_p[i]` for `p = 2³¹−1` (`p ≡ 3 mod 4`). In the same SLP model:
`FFT.SLP.karatsubaProg` computes `(a+bi)(c+di)` with **3** general multiplications
(`karatsubaProg_cost`, `karatsubaProg_correct`), the naive program uses 4
(`naiveComplexProg_cost`), and `FFT.SLP.karatsuba_beats_naive` proves the saving with
identical outputs. On the lower-bound side, `FFT.SLP.mul_lower_bound_two_of_delta` is a
general criterion, giving `FFT.SLP.complexMul_lower_bound_two`: at least **2** general
multiplications are necessary. The exact value (Winograd: 3, i.e. Karatsuba optimal) is
*not* proved here; only `2 ≤ · ≤ 3`.

## 8b. Exact optimality in the bilinear model (`BilinearLowerBound.lean`)

The straight-line model of §8 is the most general one, and there only the length-2 kernel
is settled exactly.  Winograd's theory is usually stated in the **bilinear** model: an
algorithm for a family of bilinear forms consists of `k` products
`Pᵢ(a,b) = (∑ᵣ lᵢᵣ aᵣ)·(∑ₛ rᵢₛ bₛ)` of a linear form in each argument, and every output is
a fixed linear combination of the `Pᵢ`; multiplications by field constants are free.
`FFT.Bilinear.BilinAlg` is that model and `FFT.Bilinear.BilinAlg.out` its semantics.

| Result | Lean name |
| --- | --- |
| `p` linearly independent forms need `p` products | `FFT.Bilinear.bilin_lower_bound` |
| the `n` cyclic-convolution forms are linearly independent | `FFT.Bilinear.convForm_linearIndependent` |
| hence length-`n` cyclic convolution needs `≥ n` products | `FFT.Bilinear.cyclicConv_bilinear_lower_bound` |
| the DFT algorithm attains it: **bilinear complexity of the length-`n` cyclic convolution is exactly `n`** whenever `F` has a primitive `n`-th root of unity and `n ≠ 0` in `F` | `FFT.Bilinear.convAlg`, `FFT.Bilinear.convAlg_correct`, **`FFT.Bilinear.cyclicConv_bilinear_complexity`** |
| over `M31`, length 3 is exactly 3 (cube root `omega31`) | `FFT.Bilinear.conv3Alg`, **`FFT.Bilinear.conv3_bilinear_optimal`** |
| over `M31`, **length 31 is exactly 31**, and the optimal algorithm's linear forms use only the constants `2^k`, i.e. bit rotations | **`FFT.Bilinear.cyclicConv31_M31_bilinear_complexity`** |

The last line is the sharp version of the "free twiddles" phenomenon of §6: at length 31
over `M31` the *only* essential arithmetic is the 31 pointwise products; every linear
combination in the algorithm is built from shifts and additions.  The bound is exact —
no bilinear algorithm can do better — but it is model-relative, and says nothing about
programs that multiply intermediate results with each other (the model of §8).

The bridge between the two index conventions used in the development is
`FFT.Bilinear.convForm_eq_cyclicConv` (`Fin n` subtraction versus `(k + n − i) % n`).

## 8d. Polynomial multiplication: exact bilinear complexity, and Karatsuba's optimality (`PolyMul.lean`)

In the same bilinear model, the complexity of multiplying a polynomial of degree `≤ m` by
one of degree `≤ n` is settled exactly.

| Result | Lean name |
| --- | --- |
| the `m+n+1` coefficient forms of the product are linearly independent | `FFT.Bilinear.polyMulForm_linearIndependent` |
| hence `≥ m+n+1` products are necessary | `FFT.Bilinear.polyMul_lower_bound` |
| evaluation ∘ interpolation (Toom–Cook, inverse Vandermonde) is correct | `FFT.Bilinear.toomAlg`, `FFT.Bilinear.toomAlg_correct` |
| **exact complexity `m+n+1`** over any field with `m+n+1` distinct elements | **`FFT.Bilinear.polyMul_bilinear_complexity`** |
| over `M31`, for all degrees with `m+n+1 ≤ p` | **`FFT.Bilinear.polyMul_M31_bilinear_complexity`** |
| **Karatsuba's 3 multiplications are optimal** for two linear polynomials over `M31` | **`FFT.Bilinear.karatsuba_bilinear_optimal`** |

The last line sharpens §9: in the general straight-line model only `2 ≤ · ≤ 3` is proved
for the complex/`2 × 2` product, whereas in the bilinear model the value `3` for the
polynomial product of two linear polynomials is exact.

Folding the product modulo `xⁿ − 1` turns this into a cyclic-convolution algorithm that
needs **no root of unity at all** (`FFT.Bilinear.convForm_eq_sum_polyMulForm`,
`FFT.Bilinear.cyclicToomAlg`, `FFT.Bilinear.cyclicToomAlg_correct`):

| Result | Lean name |
| --- | --- |
| length-`n` cyclic convolution: `n ≤ complexity ≤ 2n−1` over any field with `2n−1` distinct elements | **`FFT.Bilinear.cyclicConv_bilinear_bounds`** |
| the length-30 convolution of Rader's reduction over `M31`: 59 products suffice, 30 are necessary | **`FFT.Bilinear.cyclicConv30_M31_bounds`** |

The second line is the constructive counterpart of §8c: over `M31` the transform route to
the length-30 convolution is unavailable, but a Toom–Cook style bilinear algorithm with 59
general multiplications exists (against `30² = 900` for the schoolbook algorithm), and no
bilinear algorithm can go below 30.

## 8c. The sharp extension degree for Rader's length-30 convolution (`RaderThirty.lean`)

Rader's reduction turns the length-31 DFT over `M31` into a length-30 cyclic convolution,
and the convolution theorem evaluates such a convolution by three length-30 transforms —
but only over a field with a primitive 30-th root of unity, which `M31` lacks
(`FFT.M31.no_primitiveRoot_thirty`).  This file determines exactly which extensions work.

| Result | Lean name |
| --- | --- |
| `p^k ≡ 2^(k mod 4) (mod 5)` | `FFT.M31.pow_mod_five` |
| `5 ∣ p^k − 1 ↔ 4 ∣ k` | `FFT.M31.five_dvd_pow_sub_one_iff` |
| `6 ∣ p^k − 1` for every `k` | `FFT.M31.six_dvd_pow_sub_one` |
| `30 ∣ p^k − 1 ↔ 4 ∣ k` | `FFT.M31.thirty_dvd_pow_sub_one_iff` |
| **`𝔽_{p^k}` has a primitive 30-th root of unity iff `4 ∣ k`** | **`FFT.M31.exists_primitiveRoot_thirty_ext_iff`** |
| degree 4 is minimal: `𝔽_p`, `𝔽_{p²}`, `𝔽_{p³}` all fail, `𝔽_{p⁴}` succeeds | **`FFT.M31.min_extension_degree_for_thirty`** |

Consequence for implementations: the quadratic extension, which suffices for *every*
radix-2 length (§1), does **not** suffice for the transform-based evaluation of Rader's
length-30 convolution; either one pays a degree-4 extension, or that convolution is
evaluated by a short-convolution (Winograd / Agarwal–Cooley) scheme — §13 and §8b.

## 9. Executable reference and test vectors (`Reference.lean`)

Everything in this file is checked by the Lean *kernel* (`decide +kernel`), not by
`#eval`:

* the `UInt32` kernels agree with `ZMod (2³¹−1)` arithmetic on concrete values, including
  the redundant zero, and the branch-free variants agree with the `min`-based ones;
* for the explicit point `q4 = gen^(2²⁷)` of order `2⁴`, the 8-point twin coset consists
  of 8 distinct points whose second half is the inverse of the first, and the circle FFT
  round trip holds in both directions on two coefficient vectors;
* the transform agrees with `naiveCircle8`, an *independent* geometric low-degree
  extension written directly in circle coordinates (`π(x)^b₀·x^b₁·y^b₂`) — a genuine
  cross-check of the twiddle-tower construction;
* the prime-factor indexing convention is checked on a length-15 instance over `𝔽₃₁`.

## 10. Verus bridge

`verus/m31_fft.rs` is a contract skeleton whose `requires`/`ensures` clauses are direct
transliterations of the Lean theorems (each is annotated with its Lean name): Mersenne
folding, the rotation kernel with its "already reduced" postcondition, the 31-point
kernel with its overflow-free 64-bit accumulator invariant, the bit-reversal permutation
with the involution-based invariant, the quasi-canonical branch-free `add`/`sub`/`neg`/
`mul` kernels with the `QC` invariant, the lazy-reduction stage bound, the circle-FFT
butterflies, and the prime-factor index maps.

**Honest status:** no Rust/Verus toolchain is available in the environment used to
produce this repository, so that file has *not* been machine-checked; only the
mathematics behind the contracts has been. Likewise, no benchmark against existing
libraries was run, so no performance claim relative to any implementation is made here.
See `DISCREPANCIES.md` for the full trust table and for the reproduction instructions.

## 11. What was *not* formalised

The following items of the original research plan are **not** part of the verified
development, and no claim is made about them:

* operads / associahedra as a search space of FFT factorisations;
* spectral sequences of the Cooley–Tukey filtration and their degeneration;
* Čech cohomology of index coverings / register-conflict freeness;
* `K₀`/`K₁` beyond the determinant description used above, classifying spaces `BZ/n`,
  vector bundles over them, and étale-topological models of `Spec 𝔽_p`;
* the isotypic decomposition of `Rep_F(C_n)` as a natural isomorphism of functors (only
  the matrix-level diagonalisation of the cyclic shift is proved);
* Bluestein, truncated FFT, six-step/four-step transposition schedules, and NTTs over
  `𝔽_{p²}` (multiplication in the quadratic extension itself *is* formalised, §9);
* lower bounds in the general straight-line model beyond the single length-2 micro-kernel
  of §8 (the bilinear model of §8b is settled exactly for cyclic convolution).

## 12. Computable discrete logarithm on the circle group

`CircleLog.lean` closes the gap between "`C(M31)` is cyclic of order `2³¹`" and "twiddle
tables can be generated": `FFT.dlog2` is the bit-by-bit (Pohlig–Hellman) logarithm in an
arbitrary cyclic 2-group,

```
dlog2 0       g h = 0
dlog2 (m+1)   g h = 2 * dlog2 m (g*g) h              if h^(2^m) = 1
                  = 1 + 2 * dlog2 m (g*g) (h * g⁻¹)  otherwise
```

using `m` squarings per level and no search. `FFT.dlog2_spec` proves, for every `g` of
order `2^m` and every `h` in the group generated by `g`, both `g ^ dlog2 m g h = h` and
`dlog2 m g h < 2^m` (so the exponent returned is the reduced one).

Specialising to the explicit generator of `C(M31)` gives `FFT.Circle.clog`, with
`pow_clog : gen ^ clog c = c`, `clog_lt`, `clog_pow : clog (gen ^ n) = n % 2³¹`, and the
explicit isomorphism

```
FFT.Circle.zmodEquiv : Multiplicative (ZMod (2^31)) ≃* Circle M31
```

computable in both directions. Kernel-checked test vectors (`decide +kernel`) fix
`clog 1 = 0`, `clog gen = 1`, `clog (gen^100) = 100`, `clog gen⁻¹ = 2³¹ − 1` and a round
trip.

## 13. Short cyclic convolutions of length 3

`WinogradConv3.lean` adds the length-3 building block that the Rader/Agarwal–Cooley
decomposition of the length-30 convolution needs, in the same straight-line-program cost
model as the length-2 kernel of §8:

* `cyclicConv3_prog` — the CRT algorithm for `F[x]/(x³−1) ≅ F[x]/(x−1) × F[x]/(x²+x+1)`
  (one product for the linear factor, a Karatsuba step for the quadratic one): **4**
  general multiplications over any field of characteristic `≠ 3`;
* `cyclicConv3_omega` — over a field containing a primitive cube root of unity `w`, the
  three pointwise products of the 3-point DFTs: **3** general multiplications, all
  twiddles being constants and hence free in this model;
* `M31Conv3.omega31 = 1513477735` is such a root over `M31` (kernel-checked), so
  `M31Conv3.cyclicConv3_M31` records: 3 multiplications suffice over `M31`, the program is
  correct, and **no** program can use fewer than 2 (`cyclicConv3_lower_bound`). The exact
  multiplicative complexity is *not* determined here.

A kernel-checked test vector evaluates the `M31` program on `a = (3,5,7)`, `b = (11,13,17)`
and compares with the convolution computed by hand.

`SLPEval.lean` supports this: unfolding the fold-based semantics of `SLPLowerBound.lean`
with `simp` costs quadratic time and is impractical past ~20 instructions, so this file
proves one rewrite rule per instruction (`val_add`, `val_mul`, …) whose side conditions
are discharged automatically; verifying a program is then linear in its length.

## 14. The DFT as an isomorphism of algebras, and the functorial statement (`GroupAlgebraDFT.lean`)

Sections 2–3 treat the DFT as a matrix.  This file gives its structural form, which is
what makes the convolution theorem a triviality rather than a computation.

| Result | Lean name |
| --- | --- |
| orthogonality of the characters `x ↦ ζ^{x.val}` of `ℤ/n` | `FFT.sum_zchar` |
| the DFT as a morphism of `F`-algebras `F[C_n] →ₐ (ℤ/n → F)` | `FFT.dftAlgHom` |
| the inverse transform and the two round trips | `FFT.dftInvFun_dftAlgHom`, `FFT.dftAlgHom_dftInvFun` |
| **`F[C_n] ≃ₐ[F] (ℤ/n → F)`** for `ζ` primitive of order `n` and `n` invertible | **`FFT.dftAlgEquiv`** |
| convolution theorem: the product of the group algebra becomes the pointwise product | `FFT.dftAlgEquiv_mul` |
| split semisimplicity of `F[C_n]` (Maschke, split form) | `FFT.isSemisimpleRing_monoidAlgebra` |
| **equivalence of categories `Rep F C_n ≌ ModuleCat (ℤ/n → F)`** | **`FFT.repEquivPi`** |
| the same over `M31` at length 31 (twiddles `ζ = 2`, i.e. bit rotations) | `FFT.M31.dftAlgEquiv31`, `FFT.M31.repEquivPi31` |

`repEquivPi` is the functorial reading of the DFT asked for in the plan: it says that the
transform diagonalises *every* representation of `C_n`, naturally in the representation,
not merely the regular one (§2).  It is obtained by transporting Mathlib's
`Rep.equivalenceModuleMonoidAlgebra` along the ring isomorphism `dftAlgEquiv`.  The finer
statement — an explicit natural isomorphism between the forgetful functor and a functor
built from the `n` eigenspaces — is still not formalised.

## 15. Agarwal–Cooley: submultiplicativity of the bilinear complexity (`AgarwalCooley.lean`)

The bilinear model of §8b is indexed by `Fin n`; for the Chinese-remainder (Agarwal–Cooley)
construction the index must be the group itself, so this file restates the model over an
arbitrary finite group `G` (`FFT.Bilinear.ConvAlg`, `FFT.Bilinear.gconv`) and relates the
two by `ofBilinAlg` / `toZMod`.

| Result | Lean name |
| --- | --- |
| any algorithm for convolution over `G` needs `≥ \|G\|` products | `FFT.Bilinear.ConvAlg.card_le_of_computes` |
| relabelling the index group is free | `FFT.Bilinear.ConvAlg.transport_computes` |
| **tensor product of algorithms: `k₁` and `k₂` products give `k₁·k₂` for `G × H`** | **`FFT.Bilinear.tensor_computes`** |
| **`c(mn) ≤ c(m)·c(n)` for coprime `m`, `n`** | **`FFT.Bilinear.agarwalCooley`** |
| length 6 over `M31`: 6 products (a primitive 6-th root of unity exists) | `FFT.Bilinear.exists_conv6_M31` |
| length 5 over `M31`: 9 products (Toom–Cook; no 5-th root of unity exists) | `FFT.Bilinear.exists_conv5_M31` |
| **length 30 over `M31`: 54 products suffice, ≥ 30 are necessary** | **`FFT.Bilinear.cyclicConv30_M31_agarwal_cooley`** |

The length-30 convolution is the one produced by Rader's reduction of the 31-point DFT.
`M31` has no primitive 30-th root of unity (§1), so the transform algorithm is unavailable
and §8d gives `2·30 − 1 = 59` by Toom–Cook.  Splitting `30 = 6 · 5` by the Chinese
remainder theorem and tensoring improves this to `6 · 9 = 54`.  The exact value remains
undetermined: the proved bounds are `30 ≤ c ≤ 54`.

## 16. Isotypic decomposition of a cyclic action (`IsotypicDecomposition.lean`)

The module-by-module counterpart of §14: if `T` is an endomorphism of a `K`-vector space
with `T^n = 1`, `n` invertible and `ζ` primitive of order `n`, then the DFT-weighted
averages `S_j = ∑_{k<n} ζ^{−jk} T^k` are (up to the factor `n`) the projectors onto the
eigenspaces, and

| Result | Lean name |
| --- | --- |
| `T ∘ S_j = ζ^j · S_j`, so `im S_j ⊆ ker (T − ζ^j)` | `FFT.isoSum_eigen` |
| `∑_{j<n} S_j = n` (resolution of the identity, from character orthogonality) | `FFT.sum_isoSum` |
| the eigenspaces span: `⨆_{j<n} ker (T − ζ^j) = ⊤` | `FFT.cyclic_eigenspace_iSup_eq_top` |
| **`V = ⨁_{j<n} ker (T − ζ^j)`** (internal direct sum) | **`FFT.cyclic_eigenspace_isInternal`** |
| naturality: an intertwiner maps eigenspaces to eigenspaces | `FFT.mapsTo_eigenspace_of_comm` |
| over `M31` with `n = 31`, `ζ = 2` (eigenvalues are bit rotations) | `FFT.M31.cyclic31_eigenspace_isInternal` |

This is the concrete form of "the DFT diagonalises every representation of `C_n`": §14
says it as an equivalence of categories, §16 says it as an explicit direct-sum
decomposition with explicit projectors — the projectors being exactly the `n` inverse-DFT
weightings used by the algorithms.

## 17. Bilinear complexity of an algebra: the Fiduccia–Zalcstein bound (`AlgebraRank.lean`)

Every lower bound of §8b/§15 is a dimension count: `p` independent output forms need `p`
products.  That argument cannot see why multiplication in a degree-`d` field extension —
which has only `d` output coordinates — costs `2d − 1`.  This section adds the first
non-dimensional lower bound of the project, in a coordinate-free version of the bilinear
model (`FFT.Bilinear.GenAlg`: `k` products of a linear functional of the first argument
with a linear functional of the second, recombined with fixed vectors of the output space).

| Result | Lean name |
| --- | --- |
| **Fiduccia–Zalcstein**: if `x ↦ φ u x` is injective for every `u ≠ 0`, then `k ≥ dim U + dim V − 1` | **`FFT.Bilinear.GenAlg.fiducciaZalcstein`** |
| multiplication in a `d`-dimensional domain needs `≥ 2d − 1` products | `FFT.Bilinear.domain_bilinear_lower_bound` |
| evaluation/interpolation algorithm for a power basis: `2d − 1` products suffice | `FFT.Bilinear.powerBasisAlg`, `FFT.Bilinear.powerBasisAlg_computes` |
| multiplication in `F[X]/(f)` for monic `f`: at most `2·deg f − 1` products | `FFT.Bilinear.adjoinRoot_bilinear_upper` |
| **exact value `2d − 1` for a field extension with a power basis and `2d − 1` points in the base field** | **`FFT.Bilinear.ext_bilinear_complexity`** |
| over `M31`, degree `d` extension: exactly `2d − 1` products | `FFT.Bilinear.M31ext_bilinear_complexity` |
| **`𝔽_{p²}` over `M31`: exactly 3** — the three-multiplication complex/Karatsuba kernel is optimal | **`FFT.Bilinear.M31sq_bilinear_complexity`** |
| **`𝔽_{p⁴}` over `M31`: exactly 7** | **`FFT.Bilinear.M31quartic_bilinear_complexity`** |

The proof of the lower bound is the classical one: pick `dim U − 1` of the products, find
a nonzero `u` annihilated by their left functionals, and observe that the image of the
injective map `x ↦ φ u x` — of dimension `dim V` — lies in the span of the remaining
output vectors.

The hypothesis "the base field has `2d − 1` distinct elements" is necessary, not
cosmetic: over `𝔽₂` multiplication in `𝔽₈` has tensor rank 6, not `2·3 − 1 = 5`
(exhaustive computation in `analysis/tensor_rank.py`).  Over `M31` the hypothesis is
satisfied for every extension degree of practical interest.

The Alder–Strassen/Winograd bound `2 dim A − t(A)` for an algebra with `t` maximal ideals
— missing when this section was written — is now proved in §19–§21, and it does turn the
length-30 upper bound of §18 into an exact value.

## 18. Length 5 in 8 products, length 30 in 48 (`Conv5.lean`)

`ConvAlg.computes_of_tensor` reduces correctness of a bilinear convolution algorithm to a
finite identity between its coefficient tensor and the convolution tensor.  For `M31` that
identity is decided by the kernel, which makes explicit short algorithms cheap to certify.

| Result | Lean name |
| --- | --- |
| correctness of a convolution algorithm = a finite tensor identity | `FFT.Bilinear.ConvAlg.computes_of_tensor` |
| **length 5 over `M31` in 8 products** (`x⁵ − 1 = (x − 1)Φ₅`: 1 + 7) | **`FFT.Bilinear.exists_conv5_M31_eight`** |
| **length 30 over `M31` in 48 products**, at least 30 necessary | **`FFT.Bilinear.cyclicConv30_M31_48`** |

48 is exactly the Winograd target `2·30 − t(30) = 48` recorded in `CyclotomicCosets.lean`,
and improves the 54 of §15.  The matching lower bound is proved in §20, so the length-30
Rader convolution has bilinear complexity **exactly 48**.

## 19. The substitution method and the character lower bound (`Substitution.lean`, `CharacterBound.lean`)

The classical Alder–Strassen bound is obtained here without the structure theory of
algebras, by the substitution method plus multiplicative characters.

| Result | Lean name |
| --- | --- |
| `R(B × K) ≥ R(B) + 2 dim K − 1` for a multiplicative surjection `π_B` and a multiplicative `π_K` into a domain | **`FFT.Bilinear.substitution_bound`** |
| `t` jointly injective multiplicative characters into domains force `2·dim V − t` products | **`FFT.Bilinear.character_lower_bound`** |
| algebra language: a commutative algebra embedded in a product of `t` domains has `R(A) ≥ 2 dim A − t` | **`FFT.Bilinear.algebra_alder_strassen`** |

## 20. Winograd's lower bound and the exact table over `M31` (`WinogradLower.lean`, `ExactValues.lean`)

The characters for the cyclic convolution are the evaluations at the `n`-th roots of unity
in an extension field, one per `p`-cyclotomic coset; joint injectivity comes from the
Frobenius, since the coefficients live in the prime field.

| Result | Lean name |
| --- | --- |
| every algorithm for the length-`n` cyclic convolution uses `≥ 2n − t` products (`t` = number of `p`-cyclotomic cosets) | **`FFT.Bilinear.convAlg_cyclotomic_lower_bound`** |
| length 5 over `M31`: **exactly 8** | **`FFT.Bilinear.cyclicConv5_M31_bilinear_complexity`** |
| length 6 over `M31`: **exactly 6** | `FFT.Bilinear.cyclicConv6_M31_bilinear_complexity` |
| length 10 over `M31`: **exactly 16** | `FFT.Bilinear.cyclicConv10_M31_bilinear_complexity` |
| length 15 over `M31`: **exactly 24** | `FFT.Bilinear.cyclicConv15_M31_bilinear_complexity` |
| length 30 over `M31`: **exactly 48** | **`FFT.Bilinear.cyclicConv30_M31_bilinear_complexity`** |

## 21. Exact complexity of split algebras and Winograd's theorem for every length (`AlgebraSplit.lean`, `ConvExact.lean`)

The Chinese remainder theorem, in algorithmic form, supplies the algorithm that meets the
bound of §19: project to the factors of `A ≃ₐ[F] ∏ᵢ Kᵢ` (linear, free), multiply in each
factor by evaluation/interpolation (`2 dᵢ − 1` products each), recombine (free).  The total
`Σᵢ (2 dᵢ − 1) = 2 dim A − t` matches the lower bound exactly.

| Result | Lean name |
| --- | --- |
| algorithms indexed by an arbitrary finite set | `FFT.Bilinear.GenAlg.ofFintype` |
| direct sum of algorithms, `R(A₁ × ⋯ × A_t) ≤ Σ R(Aᵢ)` | `FFT.Bilinear.GenAlg.pi`, `GenAlg.pi_computes_mul` |
| transport along linear/algebra equivalences | `FFT.Bilinear.GenAlg.congr`, `GenAlg.congr_computes_mul` |
| CRT upper bound `R(A) ≤ 2 dim A − t` | `FFT.Bilinear.split_algebra_upper_bound` |
| **exact value for a split commutative algebra: `R(A) = 2 dim A − t`** | **`FFT.Bilinear.split_algebra_exact`** |
| **the same with no splitting supplied — over a finite field every reduced commutative algebra splits** | **`FFT.Bilinear.reduced_algebra_exact`** |
| `R(B) ≤ R(A)` for quotients and for subalgebras | `FFT.Bilinear.exists_genAlg_of_surjective`, `exists_genAlg_of_injective` |
| **exact complexity modulo a squarefree polynomial: `R(F[x]/(f)) = 2 deg f − t(f)`** | **`FFT.Bilinear.polyQuotient_exact`** (`PolyQuotientExact.lean`) |
| bridge `ConvAlg ↔ GenAlg` in the missing direction | `FFT.Bilinear.GenAlg.toConvAlg` |
| `F[C_n] ≅ (ℤ/n → F)` carrying multiplication to cyclic convolution | `FFT.Bilinear.groupAlgEquivFun`, `groupAlgEquivFun_mul` |
| **Winograd's theorem, exact form: `c(n) = 2n − t(n)` for every `n` invertible in `F`** | **`FFT.Bilinear.convComplexity_eq`** |
| the same over `M31`, for every `n ≤ 2³⁰` invertible in `M31` | **`FFT.Bilinear.convComplexity_M31_eq`** |
| `t(n) ≤` number of `p`-cyclotomic cosets (decidable cover condition) | `FFT.Bilinear.factorCount_le_cover` |
| `t(n)` for `n = 5, 6, 10, 15, 30` over `M31`: `2, 6, 4, 6, 12` | `FFT.Bilinear.factorCount_M31_five` … `factorCount_M31_thirty` |

Here `t(n)` is defined intrinsically as the number of maximal ideals of `F[x]/(xⁿ − 1)`
(`FFT.Bilinear.factorCount`); the last row proves the concrete counts by combining the
general theorem with the exact values of §20 — a genuine cross-check of the two independent
routes.

The Mathlib levers used are worth recording: `IsArtinianRing.equivPi` (a reduced Artinian
commutative ring is the product of its residue fields), `isArtinian_of_tower`,
`Field.powerBasisOfFiniteOfSeparable` together with the perfectness of finite fields, the
Maschke instance `IsSemisimpleRing k[G]` and `IsSemisimpleRing → IsReduced` for commutative
rings, `Module.finrank_pi_fintype`, and `Submodule.finrank_quotient_le`.

## 22. Recursive Toom–Cook with arbitrary integer evaluation points (`ToomCook.lean`)

Sections 19–21 treat evaluation/interpolation as a *bilinear* algorithm: one level, cost
measured in general multiplications.  This section formalises the *recursive* integer
algorithm `Toom-Cook (k_x, k_y, v⃗)` in full, for arbitrary numbers of limbs and arbitrary
pairwise distinct integer evaluation points.

The algorithm (`FFT.ToomCook.toomk`) is parametrised by a *size* `n`, with the invariant
`|x|, |y| < b^n`.  Above an explicit threshold it splits `x` and `y` into `k_x` resp. `k_y`
base-`b^s` limbs, reads them as polynomials, evaluates at the `k_x + k_y − 1` points,
multiplies the values **recursively**, recovers the product polynomial by Lagrange
interpolation over `ℚ` and evaluates it at the splitting radix; below the threshold it
multiplies directly.

The key structural point is the threshold itself:

* `FFT.ToomCook.tk_THETA BASE KX KY POINTS` is a natural number depending **only** on the
  base, the two limb counts and the evaluation points — its type contains no operand.  It
  is `2·c + 4` where `c = log_b (k_max · V^{k_max}) + 1` absorbs the growth caused by
  evaluating at the points (`V = 1 + Σ|v_i|`).
* `FFT.ToomCook.tk_contraction`: above `θ` the size of every subproblem,
  `partSize + c = n / max 2 (min k_x k_y) + 1 + c`, is strictly smaller than `n`,
  whatever the operands are.  This is what makes the recursion well founded; the Lean
  definition is total by construction, so termination is not an assumption.

| Result | Lean name |
| --- | --- |
| exact limb splitting and its bounds | `FFT.ToomCook.evalL_digits`, `digits_bound`, `evalL_bound` |
| operand-independent threshold `θ` | `FFT.ToomCook.tk_THETA` |
| size contraction above `θ` | **`FFT.ToomCook.tk_contraction`** |
| the algorithm | `FFT.ToomCook.toomk`, `toomkTop`, `toomkZ` |
| **correctness for all `k_x, k_y ≥ 2` and all distinct integer points** | **`FFT.ToomCook.toomk_eq`, `toomk_correctness`, `toomkZ_correctness`** |
| classical Toom-3 (`⟨0,1,−1,2,−2⟩`) as an instance | `FFT.ToomCook.toom3_correctness` |
| unbalanced instance `k_x = 3`, `k_y = 2` | `FFT.ToomCook.toom32_correctness` |

Relation to the rest of the development: §19–21 give the *cost* side of one Toom level
(evaluation at distinct points is optimal in the bilinear model: `m+n+1` products for
polynomial multiplication, `2n − t(n)` for cyclic convolution over any field, `M31`
included), while this section gives the *recursive integer* algorithm and its termination.
The two are complementary: the bilinear results say how many general multiplications a
level costs, the recursion says how the levels compose and when they stop.

What is **not** claimed: no statement about running time, cache behaviour or comparison
with any library; the interpolation step is performed with exact rational arithmetic, and
the threshold `θ` proved here is a sufficient one, not the smallest possible.


## 23. The iterative in-place radix-2 FFT (`InPlaceFFT.lean`)

Everything the development proved about the radix-2 transform before this section
concerned the *recursive* schedule `FFT.fftRec`.  Implementations — and the Verus
contracts we want to generate — run the **iterative in-place** schedule instead: permute
the input by bit reversal, then run `k` passes of butterflies over the array, pass `s`
working on blocks of `2^s` consecutive entries with twiddle base `ζ^(2^(k−s))` and
exploiting `w^(j + 2^(s−1)) = −w^j`.

| statement | Lean name |
| --- | --- |
| the schedule | `FFT.InPlace.blockBase`, `partner`, `stage`, `runStages`, `iterFFT` |
| **loop invariant**: after pass `s`, the block at `b·2^s` holds the length-`2^s` DFT (root `ζ^(2^(k−s))`) of the bit-reversed contents of that block | **`FFT.InPlace.runStages_spec`** |
| `ζ^(2^(k−1)) = −1` at every level (what makes the butterfly `±w`) | `FFT.InPlace.pow_half_eq_neg_one` |
| the `k` passes = DFT of the bit-reversed array | `FFT.InPlace.runStages_full` |
| **correctness** (bit-reversed input + `k` passes = DFT) | **`FFT.InPlace.iterFFT_eq_dft`** |
| permutation phase as a swap loop, with its invariant | `FFT.InPlace.bitrevSwaps`, `bitrevSwaps_spec`, `bitrevSwaps_full` |
| **correctness of the whole in-place algorithm** (swap loop + passes) | **`FFT.InPlace.inPlaceFFT_eq_dft`** |
| in-placeness: each pass is a disjoint union of two-element updates | `FFT.InPlace.partner_involutive`, `partner_ne`, `blockBase_pair`, `stage_congr` |
| memory safety: every index a pass reads is `< 2^k` | `FFT.InPlace.stage_reads_lt` |
| cost: `k·2^(k−1)` multiplications, `k·2^k` additions — the optimised butterfly count | `FFT.InPlace.iterMuls_eq_fftMulsOpt`, `iterAdds_eq` |
| availability over `M31`: base field no, `𝔽_{p²}` yes for every `2^k`, `k ≤ 32` | `FFT.InPlace.M31sq.exists_iterFFT_correct` |

The invariant `runStages_spec` is exactly what an imperative proof has to carry, and
`stage_congr` together with `partner_involutive`/`partner_ne` is what licenses overwriting
the array: the butterfly at `i` reads only `i` and `partner s i`, that map is a
fixed-point-free involution, so each pass touches every pair exactly once and no butterfly
reads a slot another has already written.  Section 11 of `verus/m31_fft.rs` transliterates
these statements into the corresponding Verus contracts and loop invariants.

What is **not** claimed: the arrays are modelled as functions `ℕ → F`, so the Lean
statements are about the mathematical schedule, not about Rust memory; the Verus file
remains unchecked here (no toolchain); no benchmarks were run and no comparison with any
library is made.

## 24. Package A: substitution for arbitrary algebras, radical facts, idempotent lifting (`Substitution.lean`, `RadicalLift.lean`)

The substitution machinery of §19 was stated for a bilinear map equipped with two auxiliary
projections.  Its *one-step* form is now available in the generality of Bläser's lemma: `R`
is an arbitrary unital **associative** `F`-algebra (commutativity is not assumed), the
quotient is presented as a surjective algebra homomorphism `pi : R →ₐ[F] S` (equivalently,
`S = R ⧸ I` for a two-sided ideal `I`), and the conclusion is that any algorithm of length
`k` for `R` contains an algorithm of length `k − 1` for `S`.

| statement | Lean name |
| --- | --- |
| every nonzero element is seen by some left form (take `x = 1`) | `FFT.Bilinear.exists_left_ne_of_computes` |
| **one substitution step**: nonzero kernel ⇒ length drops by one | **`FFT.Bilinear.substitution_step`** |
| numerical form: `R(R ⧸ I) < R(R)` for `I ≠ 0` | `FFT.Bilinear.bilinRank_lt_of_proper_quotient` |
| `rad A` = intersection of the maximal (two-sided) ideals | `FFT.Bilinear.radical_eq_sInf_maximal` |
| `rad A` is nilpotent, its elements are nilpotent | `FFT.Bilinear.isNilpotent_radical`, `radical_isNilpotent_mem` |
| **`A ⧸ rad A` is semisimple** | `FFT.Bilinear.isSemisimpleRing_quotient_radical` |
| **idempotents lift along `rad A`** (in a commutative ring all idempotents are central) | `FFT.Bilinear.exists_isIdempotentElem_lift` |
| complete orthogonal families of idempotents lift, i.e. a splitting of `A ⧸ rad A` is induced by a splitting of `A` | `FFT.Bilinear.exists_completeOrthogonalIdempotents_lift` |
| **`t(A) = t(A ⧸ rad A)`**: the maximal ideals of `A` are the simple factors of `A ⧸ rad A` | `FFT.Bilinear.numMaxIdeals_quotient_radical`, `maximalSpectrumQuotientRadicalEquiv` |

Deviation from the plan's phrasing, recorded for honesty: the plan asks for the step to be
indexed by "a linear form `λ` with `λ(1) ≠ 0`".  What actually makes a substitution step
work is a form that is nonzero **on the ideal being divided out** — `λ(1) ≠ 0` alone only
certifies the trivial quotient `A ⧸ A = 0`.  The Lean statement therefore takes a nonzero
`z` in the ideal and produces the form from it (`exists_left_ne_of_computes`, using
`z · 1 = z ≠ 0`), which is the argument the plan intends.

### 24.1 The ideal form, the numerical corollaries, and the equality case

| statement | Lean name |
| --- | --- |
| **substitution step, ideal form**: nonzero ideal `I` ⇒ algorithm of length `k − 1` for `A ⧸ I` | **`FFT.Bilinear.substitution_step_ideal`** |
| `R(A ⧸ I) < R(A)` | `FFT.Bilinear.bilinRank_quotient_lt` |
| **`dim (A ⧸ I) < dim A`** for `I ≠ 0` | `FFT.Bilinear.finrank_quotient_lt` |
| **`t(A ⧸ I) ≤ t(A)`** | `FFT.Bilinear.numMaxIdeals_quotient_le` |
| `t(K) = 1` for a field, `t(K³) = 3` | `FFT.Bilinear.numMaxIdeals_field`, `numMaxIdeals_cube` |
| **the plan's `t(A ⧸ I) ≥ t(A) − 1` is false** — verified counterexample `A = 𝔽₂³`, `I = ker(first projection)`: `t(A) = 3`, `t(A ⧸ I) = 1` | **`FFT.Bilinear.numMaxIdeals_quotient_not_ge`** |
| **equality case**: given the Alder–Strassen bound for the product and the two peeling (substitution) bounds, `A × B` has minimal rank ⟺ both factors do, and then `R(A × B) = R(A) + R(B)` | **`FFT.Bilinear.minimalRank_prod_iff_tight`** |

The equality-case theorem is the precise form of the plan's item 4 ("A has minimal rank iff
every substitution step is tight and every local factor has minimal rank").  Its hypotheses
record exactly what the informal statement leaves implicit: without the peeling bounds the
forward implication is *not* derivable (the Alder–Strassen bound for the factors plus
`R(A × B) ≤ R(A) + R(B)` only re-derive `R(A × B) ≤ R(A) + R(B)`).  Package B supplies the
peeling bounds for the algebras of the project's class.

## 25. Roots A, B, C: universal algebra, probability, provability logic (`Root/`)

A new `RequestProject/Root/` layer, requested as a reusable foundation for the later
packages.  Everything below is machine-checked, contains no `sorry` and adds no axioms; the
`#print axioms` audit for all of it is at the end of `RequestProject/Main.lean`.

### 25.1 Root A — universal algebra (`Root/Algebra.lean`)

| statement | Lean name |
| --- | --- |
| signature (operation symbols with *type*-valued arities), terms, algebras, homomorphisms | `Root.Signature`, `Root.Term`, `Root.SigAlgebra`, `Root.IsSigHom` |
| evaluation (fold) of a term; homomorphisms commute with it (`eval_cong`) | `Root.evalTerm`, `Root.IsSigHom.evalTerm` |
| universal property of the term algebra (absolutely free algebra) | `Root.exists_unique_evalTerm` |
| equational theory: congruence generated by axioms, free algebra, induction principle | `Root.EqRel`, `Root.FreeAlg`, `Root.FreeAlg.ind` |
| the free algebra is a model of its (substitution-closed) axioms | `Root.FreeAlg.satisfies` |
| **universal property of the free algebra** — unique homomorphism extending an interpretation | `Root.FreeAlg.exists_unique_lift`, alias `Root.free_alg_fold_unique` |
| congruences and quotient algebras with their universal property | `Root.SigCon`, `Root.SigCon.exists_unique_lift` |
| equational classes are closed under subalgebras, quotients and products (HSP) | `Root.SigSubalg.satisfies`, `Root.SigCon.satisfies`, `Root.pi_satisfies` |

Two corrections to the template supplied with the request are recorded in the file header
and in `DISCREPANCIES.md`: the algebra class is `SigAlgebra` (Mathlib already owns
`Algebra`), and the universal property must quantify over *homomorphisms* — the template's
version, with no such requirement, is false.

### 25.2 Root A — instances and the bridge to Mathlib (`Root/Instances.lean`)

| statement | Lean name |
| --- | --- |
| ring signature and its substitution-closed equational axioms | `Root.Instances.RingOp`, `RingAx`, `CommRingAx`, `ringAx_substClosed`, `commRingAx_substClosed` |
| every ring / commutative ring is a model | `ring_satisfies`, `commRing_satisfies` |
| **`IsSigHom` between rings ⟺ ring homomorphism** (both directions, bundled) | `isSigHom_ring_iff`, `isSigHom_of_ringHom`, `ringHomOfIsSigHom` |
| the free ring on a set of generators and its universal property | `exists_unique_ring_lift` |
| module signature over a scalar ring; every module is a model | `ModuleOp`, `ModuleAx`, `module_satisfies` |
| **R1CS** constraints as pairs of ring terms; satisfaction ⟺ equality of term values | `R1CS.Constraint`, `R1CS.sat_iff_evalTerm` |
| R1CS base change: satisfaction is preserved by every ring homomorphism | `R1CS.Constraint.map`, `R1CS.Constraint.sat_map` |
| **Plonk gates** `qL·a + qR·b + qO·c + qM·a·b + qC = 0` as equations of the ring signature | `Plonk.Gate`, `Plonk.sat_iff_evalTerm` |
| **AIR** transition constraints as pairs of ring terms on consecutive trace rows, with base change along a ring homomorphism preserving satisfaction | `AIR.Transition`, `AIR.Sat`, `AIR.Transition.map`, `AIR.sat_map` |
| a machine-word (ISA fragment) signature on `BitVec n` | `BitOp`, `instSigAlgebraBitVec` |
| **fields are not an equational class** (products of fields need not be fields) | `field_not_equational` |

The last row is a limitation of the framework, proved rather than assumed: it explains why
the field-specific results of the project (`M31`, `𝔽_{p^k}`) cannot be obtained by merely
instantiating an equational theory.

### 25.3 Root A — integration with the existing modules (`Root/Bridge.lean`)

| statement | Lean name |
| --- | --- |
| the coordinate model embeds in the coordinate-free one, with the same number of products | `FFT.Bilinear.BilinAlg.toGenAlg`, `toGenAlg_eval` |
| correctness is preserved in both directions | `FFT.Bilinear.BilinAlg.toGenAlg_computes_iff` |
| hence the Fiduccia–Zalcstein bound applies to `BilinAlg` as well | `FFT.Bilinear.BilinAlg.fiducciaZalcstein` |
| an ideal is a congruence of the ring signature | `Root.Instances.conOfIdeal` |
| the universal-algebra quotient is canonically isomorphic to `R ⧸ I`, as algebras | `quotEquivIdealQuotient`, `isSigHom_quotEquivIdealQuotient` |
| the universal property of `R ⧸ I` as an instance of the generic one | `exists_unique_lift_of_ideal` |

### 25.4 Root B — probability monad and information metrics (`Root/Prob.lean`)

| statement | Lean name |
| --- | --- |
| probability measures, `pure`, `bind` (kernel measurable), the three monad laws | `Root.Prob`, `Prob.pure`, `Prob.bind`, `pure_bind`, `bind_pure`, `bind_assoc` |
| total variation as `sup` over measurable sets; non-negativity, `≤ 1`, symmetry, triangle inequality | `Prob.TV`, `TV_nonneg`, `TV_le_one`, `TV_comm`, `TV_triangle` |
| **data-processing inequality**, deterministic post-processing | `Prob.TV_map_le` |
| finite distributions, `pure`, `bind`, monad laws | `Root.FinProb`, `FinProb.pure_bind`, `bind_pure`, `bind_assoc` |
| **data-processing inequality for arbitrary Markov kernels** | `FinProb.tv_bind_le` |
| Kullback–Leibler divergence and Gibbs' inequality `KL ≥ 0` | `FinProb.kl`, `FinProb.kl_nonneg` |

`bind` on measures carries a measurability hypothesis on the kernel: without it
`Measure.bind` need not be a probability measure, so the unconditional `Monad` instance of
the template cannot exist.

### 25.5 Root C — modal logic of provability (`Root/Modal.lean`)

| statement | Lean name |
| --- | --- |
| modal syntax, Kripke frames, satisfaction, validity | `Root.Modal.Form`, `Root.Modal.Sat`, `Root.Modal.ValidOn` |
| axiom `K` valid on every frame; necessitation preserves validity | `valid_K`, `valid_nec` |
| axiom `4` valid on transitive frames | `valid_four` |
| **Löb axiom valid on transitive, converse well-founded frames** | `valid_loeb` |
| the hypothesis is needed: the Löb axiom fails on the reflexive one-point frame | `not_valid_loeb_reflexive` |
| Hilbert–Bernays–Löb derivability conditions | `Root.Modal.Derivability` |
| **Löb's rule** and **Löb's theorem** from those conditions plus a Gödel fixed point | `Derivability.loeb_rule`, `Derivability.loeb` |
| a false `Box`-sound proposition has no fixed point; the conditions are consistent | `Derivability.no_fix_of_not`, `derivability_id` |

No axioms were added: the `box_distrib` / `box_trans` / `lob` of the template appear as
hypotheses (fields of `Derivability`) and as theorems, never as `axiom` declarations.

## 26. Package B — peeling factors off a product, and Package D on the Root

### 26.1 Root A extended: the signature of an `F`-algebra (`Root/Instances.lean`)

| statement | Lean name |
| --- | --- |
| signature of a unital associative `F`-algebra (ring operations plus one unary operation per scalar) | `Root.Instances.AlgOp`, `instSigAlgebraAlgebra` |
| its equational axioms; every `F`-algebra is a model; substitution-closed | `AlgAx`, `CommAlgAx`, `alg_satisfies`, `commAlg_satisfies`, `algAx_substClosed` |
| bridge to Mathlib: signature homomorphism ⟺ `AlgHom` | `isSigHom_alg_iff`, `isSigHom_of_algHom`, `algHomOfIsSigHom` |
| **group algebra `F[G]`** (in particular `F[C_n]`, whose multiplication is the cyclic convolution) as a model | `groupAlgebra_satisfies`, `groupAlgebra_sigMul`, `groupAlgebra_commAx` |
| **polynomial quotient `F[x]/(f)`** and the cyclic convolution algebra `F[x]/(xⁿ − 1)` as models | `PolyQuot`, `CyclicConvAlg`, `polyQuot_satisfies`, `cyclicConvAlg_satisfies` |
| an ideal of an algebra is a congruence; the universal-algebra quotient *is* `A ⧸ I` as an algebra | `conOfIdealAlg`, `quotEquivIdealQuotientAlg`, `isSigHom_quotEquivIdealQuotientAlg` |
| the universal property of `A ⧸ I` for algebras, for free | `exists_unique_lift_of_idealAlg` |
| **local factors `A ⧸ mᵏ`** and the projections between them | `localFactor_satisfies`, `localFactorProj`, `isSigHom_localFactorProj` |

### 26.2 Package B — the peeling bounds (`Peeling.lean`)

| statement | Lean name |
| --- | --- |
| `R(C × K) ≥ R(C) + 2 dim K − 1` for `K` a domain (residue field) | `FFT.Bilinear.bilinRank_peel_domain` |
| `R(A) ≥ R(B) + 2 dim (ker π)` for `π : A ↠ B` reflecting units | `bilinRank_peel_unitReflecting` |
| iterating over the factors of a finite product of domains | `bilinRank_peel_pi` |
| **`R(C × B) ≥ R(C) + 2 dim B − t(B)` for `B` reduced** — the hypothesis `hpeel` left open in Package A | `bilinRank_peel_reduced` |
| a local algebra with a unit-reflecting character has `t = 1` | `numMaxIdeals_eq_one_of_character` |
| **`R(A × B) ≥ R(B) + 2 dim A − 1` for `A` local** | `bilinRank_peel_local_left` |
| **the equality case, unconditionally**, for `A` local with residue field `F` and `B` reduced: `A × B` has minimal rank ⟺ both factors do, and then `R(A × B) = R(A) + R(B)` | `minimalRank_prod_local_reduced` |

The conditional statement of Package A (`minimalRank_prod_iff_tight`) is thereby discharged
for this class: all three of its hypotheses are now theorems.

### 26.3 Package D — the generator over products of signature algebras (`WinogradGenerator.lean`)

| statement | Lean name |
| --- | --- |
| universal property of the product of signature algebras; projections are homomorphisms | `Root.exists_unique_pi_lift`, `Root.isSigHom_pi_proj` |
| for `AlgOp F` the universal-algebra product structure is the product algebra | `Root.Instances.algOp_pi_op`, `isSigHom_algOp_proj` |
| `R(∏ᵢ Aᵢ) ≤ Σᵢ R(Aᵢ)` | `FFT.Bilinear.bilinRank_pi_le` |
| **the Winograd/CRT generator** for `A ≃ₐ ∏ᵢ Kᵢ` with power bases — fields *or* local factors — of length `Σᵢ (2 dᵢ − 1)` | `winograd_generator` |
| the same, consuming a family of ideals whose comparison map is bijective | `crtHom`, `winograd_generator_of_ideals`, `bilinRank_le_of_ideals` |
| **exact rank of `local × reduced`**: `R(A × B) = 2 dim (A × B) − t(A × B)` | `bilinRank_local_prod_reduced_of_upper`, `bilinRank_local_prod_reduced`, `minimalRank_local_prod_reduced` |
| over `M31`: a length-`k` short product together with a length-`n` cyclic convolution costs exactly `2(k + n) − (1 + t(n))` | `FFT.Bilinear.M31.bilinRank_truncPoly_prod_cyclic` |

This is the first exact value in the development for a product containing a factor **with
nilpotents**; the lower bound is precisely the peeling bound of §26.2, so no algorithm can
share work between the nilpotent block and the semisimple one.

As everywhere else in this repository, these are statements about the bilinear
(non-scalar multiplication) cost model only; no timing measurement was performed.

### 26.4 Package B, continued — products of *several* local factors (`PeelingLocalPi.lean`, `M31LocalProducts.lean`)

§26.2 peels a single local factor.  The algebras of the project appear after the
Chinese-remainder decomposition as a *family* `A ≅ ∏ᵢ Kᵢ` of local factors, so the peeling
bound is iterated over the whole family.

| statement | Lean name |
| --- | --- |
| `R = 0` and `t = 0` for the zero algebra (base case of the inductions) | `FFT.Bilinear.bilinRank_subsingleton`, `numMaxIdeals_subsingleton` |
| `t(∏ᵢ Kᵢ) = m` for `m` local factors with residue field `F` | `numMaxIdeals_pi_local` |
| **`R((∏ᵢ Kᵢ) × C) ≥ R(C) + 2 dim (∏ᵢ Kᵢ) − m`** for an arbitrary partner `C` | `bilinRank_peel_local_pi` |
| **the Alder–Strassen bound `2 dim (∏ᵢ Kᵢ) ≤ R(∏ᵢ Kᵢ) + m`, unconditionally** | `alderStrassen_pi_local` |
| **the equality case: `∏ᵢ Kᵢ` has minimal rank ⟺ every `Kᵢ` has minimal rank** | `minimalRank_pi_local` |
| in that case `R(∏ᵢ Kᵢ) = 2 dim (∏ᵢ Kᵢ) − m` | `bilinRank_pi_local_of_minimal` |
| over `M31`: a **batch of short products** of lengths `k₀,…,k_{m−1}` costs exactly `2 Σᵢ kᵢ − m`, i.e. the sum `Σᵢ (2kᵢ − 1)` of the individual optimal costs | `FFT.Bilinear.M31.bilinRank_pi_truncPoly_M31`, `bilinRank_pi_truncPoly_M31_eq_sum` |

The last line is a *non-sharing* statement: batching several truncated ("short") products of
different lengths into one bilinear algorithm cannot save a single general multiplication
compared with running the individually optimal algorithms.  Again this concerns the bilinear
cost model only; no timing measurement was performed.

### 26.5 Alder–Strassen for **every** finite-dimensional commutative algebra (`AlderStrassen.lean`)

The research priority §3.1 of `PLAN_FALA3.md` ("full Alder–Strassen with nilpotents") is now
a theorem.  The previous proofs covered reduced algebras (characters into the residue fields)
and local algebras with residue field `F`; algebras with nilpotents *and* residue-field
extensions were out of reach.  The peeling bound of Package B closes the gap in one step.

| statement | Lean name |
| --- | --- |
| `2 dim B ≤ R(B) + t(B)` for `B` reduced | `FFT.Bilinear.alderStrassen_reduced` |
| `A ↠ A ⧸ rad A` reflects units (the radical of an Artinian ring is nilpotent) | `isUnit_of_isUnit_quotient_jacobson` |
| **`2 dim A ≤ R(A) + t(A)` for every finite-dimensional commutative `F`-algebra `A`** | `alderStrassen` |
| hence minimal rank ⟺ the value is reached from above | `minimalRank_iff_le` |
| the equality case of Package A now needs only the peeling hypotheses | `minimalRank_prod_iff_peel` |
| for the cyclic convolution of **arbitrary** length `n` (no invertibility of `n` required): `R(F[C_n]) ≥ 2n − t(n)` | `alderStrassen_cyclicAlgebra` |

Proof: `R(A) ≥ R(A ⧸ rad A) + 2 dim (rad A)` by peeling along the unit-reflecting surjection
`A ↠ A ⧸ rad A`; the quotient is reduced, so `R(A ⧸ rad A) ≥ 2 dim (A ⧸ rad A) − t(A ⧸ rad A)`;
finally `dim A = dim (rad A) + dim (A ⧸ rad A)` and `t(A) = t(A ⧸ rad A)`.

## 27. Root D: coding theory and a proximity gap for Reed–Solomon codes (`Root/CodingTheory/`)

The coding-theory layer requested on top of the existing roots.  Everything below is proved
(clean `lake build`, no `sorry`, no added axioms; the audit in `RequestProject/Main.lean`
lists `propext`, `Classical.choice`, `Quot.sound` only).

### 27.1 The Hamming metric and linear codes (`Hamming.lean`)

| statement | Lean name |
| --- | --- |
| Hamming distance, agreement set, relative distance (in `[0,1]`) | `Root.CodingTheory.hammingDistance`, `agreementSet`, `relativeHammingDistance` |
| symmetry, vanishing iff equal, triangle inequality | `hammingDistance_comm`, `hammingDistance_eq_zero`, `hammingDistance_triangle` |
| distance = weight of the difference (linear codes) | `hammingDistance_eq_weight_sub` |
| minimum distance of a linear code and its characterisation | `minDistance`, `minDistance_eq`, `minDistance_le_hammingDistance` |
| unique decoding below half the minimum distance | `eq_of_lt_half_minDistance` |

### 27.2 Interpolation, zeros, Schwartz–Zippel (`PolynomialInterpolation.lean`)

| statement | Lean name |
| --- | --- |
| **L1** — exactly one polynomial of degree `< n` through `n` distinct points | `existsUnique_interpolant` (with `interpolant`, `eq_of_degree_lt_of_eval_eq`) |
| **L2** — a nonzero polynomial has at most `deg` zeros in any finite set; `< d` zeros if its degree is `< d` | `card_roots_in_le`, `card_roots_in_lt_of_degree_lt` |
| **Schwartz–Zippel** (one variable) via the project's probability layer | `schwartz_zippel` |

The probability layer of `Root/Prob.lean` was extended for this: the uniform distribution
`Root.FinProb.uniform` and the probability `Root.FinProb.probOf` of an event, with
`probOf_uniform : probOf (uniform α) s = |s| / |α|`.

### 27.3 Reed–Solomon codes (`ReedSolomon.lean`)

| statement | Lean name |
| --- | --- |
| the code `RS_d(D) ⊆ (↥D → F)` as a submodule | `reedSolomonCode` |
| every nonzero codeword has weight `≥ |D| − d + 1` | `reedSolomon_weight_ge` |
| **the minimum distance is exactly `|D| − d + 1`** (`1 ≤ d ≤ |D|`) | `reedSolomon_minDistance` |
| unique decoding inside radius `(|D| − d + 1)/2` | `reedSolomon_unique_decoding` |

### 27.4 The local test and its acceptance probability (`LocalTests.lean`)

The verifier samples a uniformly random `s`-element subset `S ⊆ D` and accepts iff `f|_S`
is consistent with some polynomial of degree `< k`.

| statement | Lean name |
| --- | --- |
| accepting condition, accepting samples, acceptance probability `α(f)` | `IsLocallyConsistent`, `goodSubsets`, `acceptProb` |
| `α(f) ∈ [0,1]`, and `α(f)` **is** a probability in the sense of `Root/Prob.lean` | `acceptProb_nonneg`, `acceptProb_le_one`, `acceptProb_eq_probOf_uniform` |
| distance of a word to the code, defined with `Finset.min'` | `distToCode`, `distToCode_le` |
| **L3** — the approximation is attained: an explicit codeword at distance `distToCode` | `exists_poly_dist_eq_distToCode`, `exists_poly_relativeDistance_eq` |
| agreement of `f` with any codeword is at most `|D| − distToCode` | `card_polyAgreement_le` |

### 27.5 T1 — a proximity gap for the subset test (`ProximityGapSubsets.lean`)

Write `n = |D|`.  Assume `k ≤ s` and that **no** polynomial of degree `< k` agrees with `f`
on more than `m` positions.

| statement | Lean name |
| --- | --- |
| an accepting sample determines its witness (interpolant on any `k` of its points) | `eq_candidate_of_consistent` |
| accepting samples live inside the agreement sets of the `C(n,k)` candidate interpolants | `goodSubsets_subset_biUnion` |
| counting bound `#accepting ≤ C(n,k)·C(m,s)` | `card_goodSubsets_le` |
| **T1**: `α(f) ≤ C(n,k)·C(m,s)/C(n,s)` | `proximity_gap_subsets` |
| version with the distance to the code | `proximity_gap_distToCode` |
| **proximity gap** (contrapositive): `α(f)` above the threshold ⇒ an explicit `p` of degree `< k` with `Δ(f, ev p) < (n − m)/n` | `proximity_gap`, `exists_agreement_gt_of_acceptProb` |
| **sharpness**: agreement `a` forces `α(f) ≥ C(a,s)/C(n,s)` | `le_acceptProb_of_agreement` |

The bound is non-vacuous exactly where one expects: for `m < s` it reads `α(f) = 0`, and for
`m ≥ s` the ratio `C(m,s)/C(n,s)` decays like `(m/n)^s`, so the factor `C(n,k)` is beaten as
soon as `s` is large compared with `k·log n / log(n/m)`.

The formula proposed for T1 in the request is *not* the one proved here; see the note in
`DISCREPANCIES.md`.

### 27.6 Affine lines (`AffineSubspaces.lean`)

| statement | Lean name |
| --- | --- |
| the affine parametrisation `t ↦ a + t·b` and its evaluation | `lineMap`, `eval_lineMap` |
| **L4** — restriction to a line does not raise the degree | `natDegree_comp_lineMap_le`, `degree_comp_lineMap_lt` |
| **completeness of the line test**: a codeword restricts to a codeword | `reedSolomon_restrict_line` |

The soundness direction (T2, the FRI-style gap `δ_d(f) ≤ 1 − α(f) + c·d/q`) is **not**
proved; it is recorded as an open item (O14) in `DISCREPANCIES.md`.

### 27.7 Correlated agreement on a line of words (`ProximityGapLines.lean`)

For `f₀, f₁ : ↥D → F` and `z ∈ F` put `lineComb f₀ f₁ z = f₀ + z·f₁`.

| statement | Lean name |
| --- | --- |
| **two good points suffice**: if `f₀ + z₁·f₁` and `f₀ + z₂·f₁` (`z₁ ≠ z₂`) are both within Hamming distance `e` of `RS_k(D)`, then there are codewords `q₀, q₁` of degree `< k` and one **common** set `T` with `|T| ≥ |D| − 2e` on which `f₀ = q₀` and `f₁ = q₁` | `correlated_agreement_of_two` |
| probabilistic form: acceptance probability `> 1/|F|` over a uniform `z` gives the same conclusion | `proximity_gap_lines` |

The codewords are constructed explicitly from the two local witnesses, so neither a large
field nor list decoding is needed.

### 27.8 Mutual correlated agreement (`MCA.lean`)

| statement | Lean name |
| --- | --- |
| `(S,δ)`-closeness of a word, and of a whole line, to the code | `IsCloseOn`, `LineCloseOn` |
| **L1 (line closure)**: if `f₀` and `f₁` agree with codewords on the same `S`, so does every point of the line | `line_closure` |
| bad points of a line and `ε_mca` (per line and its maximum over all lines) | `IsBad`, `badSet`, `epsMCA`, `epsMCAmax` |
| **MCA ⇒ correlated agreement**: if a random point of the line is `e`-close with probability `> ε_mca`, one single `S` with `|S| ≥ |D| − e` works for the whole line | `correlatedAgreement_of_epsMCA_lt` |
| **unique-decoding row**: if `3e < |D| − k + 1` then at most `|D|` points of a line are bad | `card_badSet_le` |
| hence `ε_mca ≤ |D|/|F|`, for one line and for the maximum over all lines | `epsMCA_le`, `epsMCAmax_le` |
| headline form: acceptance probability `> |D|/|F|` on a line ⇒ one common `S` with `|S| ≥ |D| − e` for the whole line | `correlatedAgreement_of_prob_gt` |

The proof of the last row is self-contained: either the set of good `z` is small (and the bad
set is contained in it), or two good points already force a common agreement set `T`; a
disjointness/counting argument then pushes `|T|` up to `|D| − e`, and every bad point must
contribute a distinct position outside `T`.

The list-decoding (Johnson-radius) rows of that table and the asymptotic threshold
`δ* = 1 − √ρ` are **not** proved; see O16 and O17 in `DISCREPANCIES.md`.

### 27.9 A Johnson-type list-size bound (`Johnson.lean`)

Write `n = |D|` and let `decodingList k t f` be the set of codewords of degree `< k` agreeing
with `f` in at least `t` positions.

| statement | Lean name |
| --- | --- |
| two distinct codewords agree in at most `k − 1` positions | `card_agreementSet_le_of_ne` |
| first and second moment of the "pass count" `m(x) = #{g in the list : g x = f x}` | `sum_passCount`, `sum_passCount_sq`, `sum_passCount_sq_le`, `le_sum_passCount` |
| **list-size bound** `L·(t² − n(k−1)) ≤ n·t` (no hypothesis on `t`) | `johnson_list_bound` |
| explicit form `L ≤ n·t/(t² − n(k−1))` when `n(k−1) < t²` | `card_decodingList_le` |
| in the unique-decoding regime `n + (k−1) < 2t` the list has at most one element | `card_decodingList_le_one` |

The proof is the classical second-moment argument: double counting for `∑ m(x)` and
`∑ m(x)²`, the pairwise agreement bound `k − 1`, and Cauchy–Schwarz.  It is *not* the full
Johnson bound `t > √(n·k)` in its sharpest constant, but it is a proved, explicit list-size
bound valid beyond the unique-decoding radius.

### 27.10 Correlated agreement from list decoding (`CorrelatedAgreement.lean`)

Write `n = |D|`, `G = {z ∈ F : Δ(f₀ + z·f₁, C) ≤ e}` (`goodZ`) and

`Λ(k,t) = max_{g : ↥D → F} #{c ∈ C of degree < k : |agree(g,c)| ≥ t}`  (`listSizeMax`),

so `Λ(k, n − e)` is the `Λ(C,e)` of the work package.

| statement | Lean name |
| --- | --- |
| two points `z₀ ≠ z` of a line and local witnesses `p₀, p` determine a pair `q₀, q₁` of degree `< k` with `q₀ + z₀·q₁ = p₀`, `q₀ + z·q₁ = p` | `exists_line_pair` |
| that pair agrees with `f₀, f₁` on a common set of `≥ n − 2e` positions | `card_inter_polyAgreement_ge_of_pair` |
| `Λ ≥ 1` | `one_le_listSizeMax` |
| **Theorem CA**: `2·e·Λ(k, n − 2e) + 1 < |G|` ⇒ there are `q₀, q₁` of degree `< k` with `#{x : f₀ x = q₀ x ∧ f₁ x = q₁ x} ≥ n − e` | `correlatedAgreement_of_card_goodZ_gt` |

Theorem CA carries **no** hypothesis on `k`, `e`, `n` or `|F|`.  The proof fixes one good
`z₀ ≠ 0`; every other good `z` yields the pair `(Q₀ z, Q₁ z)` above, so `z ↦ Q₀ z|_D` maps the
good values into a list-decoding list of `f₀` at agreement `n − 2e` (size `≤ Λ`); two good
values in the same fibre carry the *same* pair (this is where `z₀ ≠ 0` is used), and the sets
`A_z \ T` are then pairwise disjoint and nonempty unless `|T| ≥ n − e`, bounding each fibre by
`n − |T| ≤ 2e`.

### 27.11 The MCA row beyond unique decoding (`MCAJohnson.lean`)

| statement | Lean name |
| --- | --- |
| two polynomials of degree `< k` agreeing on `≥ k` positions of `D` agree on `D` | `eval_eq_of_card_agreement_ge` |
| **table row**: if `2e + k ≤ n` then `#bad ≤ n·Λ(k, n − 2e)` | `card_badSet_le_listSizeMax` |
| hence `ε_mca ≤ n·Λ/|F|`, per line and for the maximum over lines | `epsMCA_le_listSizeMax`, `epsMCAmax_le_listSizeMax` |
| headline form: acceptance probability `> n·Λ/|F|` ⇒ one common `S`, `|S| ≥ n − e`, for the whole line | `correlatedAgreement_of_prob_gt_johnson` |
| `Λ(k,t) ≤ n·t/(t² − n(k−1))` when `n(k−1) < t²` | `listSizeMax_le_johnson` |
| `2e + √(n(k−1)) < n` implies `2e + k ≤ n` and the Johnson condition at `t = n − 2e` | `half_johnson_conditions` |
| **explicit bound**: `2e + √(n(k−1)) < n` ⇒ `ε_mca ≤ n·( n·t/(t² − n(k−1)) )/|F|`, `t = n − 2e` | `epsMCAmax_le_johnson` |
| **relative form**: with `ρ = (k−1)/n`, `δ = e/n` and `2δ + √ρ < 1`, `ε_mca ≤ n·C(δ,ρ)/|F|`, `C(δ,ρ) = (1 − 2δ)/((1 − 2δ)² − ρ)` independent of `n` | `epsMCAmax_le_relative` |

This is exactly the shape `ε_mca(C,e) ≤ n·Λ/|F|` requested in the work package, with `Λ` a
list-decoding quantity controlled by the Johnson bound of §27.9.  **Scope, stated honestly.**
The regime reached is `2δ + √ρ < 1`, i.e. `δ < (1 − √ρ)/2` with `δ = e/n`, `ρ = (k−1)/n`:
*half* of the Johnson radius, and with `Λ` taken at radius `2e` rather than `e`.  The reason
is structural: correlated agreement is extracted from *two* good points of the line, whose
local witnesses are only guaranteed to overlap in `n − 2e` positions.  The full threshold
`δ* = 1 − √ρ` of the work package is **not** proved here (O17), and the requested form of
Theorem CA with the threshold `Λ(C,e)` (rather than `2e·Λ(C,2e)`) is not proved either — see
O18 in `DISCREPANCIES.md`.  Note also that the new row is *incomparable* with the
unique-decoding row of §27.8 (`3e < n − k + 1`, i.e. `δ < (1 − ρ)/3`): the new one is stronger
for low rates (`ρ < 1/4`), the old one for high rates.

## 28. Guruswami–Sudan interpolation, list decoding and the MCA threshold

This section documents the files added for the GS/MCA Johnson-regime work package:
`MultivariateInterpolation.lean`, `ListDecodingGS.lean`, `MCAJohnsonGS.lean`,
`CorrelatedAgreementRefined.lean`, and the Python analyses in `analysis/`.

Throughout, bivariate polynomials are modelled as `F[X][X] = Polynomial (Polynomial F)`:
the **inner** variable is `X`, the **outer** one is `Y`, so `Q.coeff j` is the coefficient of
`Yʲ` and is itself a polynomial in `X`.  All names below live in `Root.CodingTheory` (the
interpolation layer in the sub-namespace `Root.CodingTheory.GS`).

### 28.1 Weighted degree and multiplicity (`MultivariateInterpolation.lean`)

| statement | Lean name |
| --- | --- |
| translation `p(X) ↦ p(X + α)` as a ring hom, and `Q(X,Y) ↦ Q(X + α, Y + β)` | `GS.shiftX`, `GS.shiftBiv` |
| `wdeg_{1,k}(Q) < L`: `∀ j, deg(Q.coeff j) + k·j < L` | `GS.WdegLt` |
| zero of multiplicity `≥ m` at `(α,β)`: all coefficients of `Q(X+α, Y+β)` of total degree `< m` vanish | `GS.HasMultAt` |
| `(X − α)^m ∣ Q(X, p(X))` whenever `Q` has multiplicity `≥ m` at `(α, p(α))` | `GS.sub_pow_dvd_eval_of_hasMultAt` |
| `deg Q(X, p(X)) < L` when `deg p < k` and `wdeg_{1,k}(Q) < L` | `GS.degree_eval_lt` |
| if moreover `Q` has multiplicity `≥ m` at `(x, p(x))` for all `x` in a set `A` with `L ≤ m·|A|`, then `Q(X, p(X)) = 0` | `GS.eval_eq_zero_of_agreement` |
| **factor step**: under the same hypotheses, `(Y − p) ∣ Q` in `F[X][Y]` | `GS.Y_sub_dvd_of_agreement` |
| the monomial index set `{(a,b) : a + k·b < L}` and its cardinality bound `L² ≤ 2k·#monIdx k L` | `GS.monIdx`, `GS.card_monIdx_ge` |
| `2·#monIdx 1 m = m(m+1)` (the number of multiplicity constraints per point) | `GS.card_monIdx_one` |
| the interpolation constraints as an `F`-linear map | `GS.interpMap` |
| **GS interpolation, counting form**: `#D·#monIdx 1 m < #monIdx k L` ⇒ `∃ Q ≠ 0`, `wdeg_{1,k}(Q) < L`, multiplicity `≥ m` at every `(x, f x)` | `GS.exists_interpolating_of_card` |
| the same with the constraint count written `#D·m(m+1)/2` | `GS.exists_interpolating` |
| **Johnson-regime form**: `k·#D·(m+1) < m·t²` ⇒ such a `Q` exists with `wdeg_{1,k}(Q) < m·t` | `GS.exists_interpolating_of_johnson` |

The existence proof is pure linear algebra: `interpMap` maps a space of dimension
`#monIdx k L` into one of dimension `#D · #monIdx 1 m`, so it has a nonzero kernel as soon as
the source is bigger.  The monomial count `L² ≤ 2k·#monIdx k L` is proved by strong induction
on `L`, peeling the monomials with `b = 0` (`GS.card_monIdx_step`).

### 28.2 List decoding via factorisation (`ListDecodingGS.lean`)

| statement | Lean name |
| --- | --- |
| `wdeg_{1,k}(Q) < L`, `Q ≠ 0` ⇒ `k·deg_Y Q < L` | `GS.natDegree_lt_of_wdegLt` |
| distinct polynomials `p` with `Q(X,p) = 0` are roots of `Q` viewed over `Frac F[X]`, hence at most `deg_Y Q` of them | `GS.card_le_natDegree_of_eval_zero` |
| **GS list-size bound**: if `k·#D·(m+1) < m·t²` and every `p ∈ S` has `deg p < k` and agrees with `f` on `≥ t` points of `D`, then `k·#S < m·t` | `GS.gs_list_bound` |
| the same for the code-side list of a word `g` | `card_decodingList_lt_gs` |
| **`k·Λ(k,t) < m·t`** under `k·#D·(m+1) < m·t²` | `listSizeMax_le_gs` |

This is the list-size bound at the *full* Johnson radius: `k·n·(m+1) < m·t²` is
`t > √(k n (1 + 1/m))`, i.e. `t/n > √ρ·(1 + 1/m)^{1/2}`, and the list size is then
`< m·t/k ≈ (m/√ρ)`, bounded independently of `n`.

### 28.3 The MCA error bound with the GS list size (`MCAJohnsonGS.lean`)

| statement | Lean name |
| --- | --- |
| `ε_mca(C,e) ≤ n·(m·t/k)/|F|` with `t = n − 2e`, under `1 ≤ k ≤ n`, `2e + k ≤ n`, `k·n·(m+1) < m·t²` | `epsMCAmax_le_gs` |
| relative form: `ρ = k/n`, `δ = e/n`, `2δ + (1 + 1/(2m))√ρ < 1` ⇒ `ε_mca ≤ n·(m(1−2δ)/ρ)/|F|` | `epsMCAmax_le_gs_relative` |
| numerical core for concrete instances | `epsMCAmax_le_two_pow_of_bound` |
| `ρ = 1/2`, `n = 2²⁰`, `m = 4`, `e = 109801`, `|F| ≥ 2¹⁵¹` ⇒ `ε_mca ≤ 2⁻¹²⁸` | `threshold_rho_half` |
| `ρ = 1/4`, `n = 2²⁰`, `m = 4`, `e = 231202`, `|F| ≥ 2¹⁵²` ⇒ `ε_mca ≤ 2⁻¹²⁸` | `threshold_rho_quarter` |
| `ρ = 1/8`, `n = 2²⁰`, `m = 4`, `e = 317044`, `|F| ≥ 2¹⁵²` ⇒ `ε_mca ≤ 2⁻¹²⁸` | `threshold_rho_eighth` |
| `ρ = 1/16`, `n = 2²⁰`, `m = 4`, `e = 377745`, `|F| ≥ 2¹⁵³` ⇒ `ε_mca ≤ 2⁻¹²⁸` | `threshold_rho_sixteenth` |
| for every `ρ, δ` with `2δ + √ρ < 1` there is a constant `C(ρ,δ)` with `ε_mca ≤ n·C/|F|` for every domain | `exists_const_epsMCAmax_le` |

**Scope.**  The radius reached is `δ < (1 − √ρ)/2`, *half* the Johnson radius.  The obstruction
is no longer the list size — §28.2 supplies it at the full Johnson radius — but the extraction
of correlated agreement from two points of a line (§27.10), which consumes `Λ` at radius `2e`.

### 28.4 Correlated agreement with no list-size factor (`CorrelatedAgreementRefined.lean`)

| statement | Lean name |
| --- | --- |
| **CA, third-radius form**: `1 ≤ k`, `k + 3e ≤ n` and `2e + 1 < |G|` ⇒ a single pair `(q₀,q₁)` of degree `< k` agrees with `(f₀,f₁)` on `≥ n − e` positions | `correlatedAgreement_of_card_goodZ_gt_third` |
| counting half of the bad-set bound, isolated for reuse: correlated agreement on `T` ⇒ `#bad ≤ n − |T|` | `card_badSet_le_card_compl` |
| **`#bad ≤ 2e + 1`** whenever `k + 3e ≤ n` | `card_badSet_le_third` |
| `ε_mca ≤ (2e + 1)/|F|`, per line and for the maximum over lines | `epsMCA_le_third`, `epsMCAmax_le_third` |
| headline form: acceptance probability `> (2e+1)/|F|` ⇒ one common `S` with `|S| ≥ n − e` | `correlatedAgreement_of_prob_gt_third` |
| `ρ = 1/2`, `n = 2²⁰`, `e = 174762` (`δ = 1/6`), `|F| ≥ 2¹⁴⁷` ⇒ `ε_mca ≤ 2⁻¹²⁸` | `threshold_rho_half_third` |
| `ρ = 1/4`, `n = 2²⁰`, `e = 262144` (`δ = 1/4`), `|F| ≥ 2¹⁴⁸` ⇒ `ε_mca ≤ 2⁻¹²⁸` | `threshold_rho_quarter_third` |

The proof observes that two good points already force a candidate pair `(q₀,q₁)` with a common
agreement set `T`, `|T| ≥ n − 2e`; when `n − 3e ≥ k`, *every* good `z` has its local witness
equal to `q₀ + z·q₁` on all of `D`, and the sets `A_z \ T` are then nonempty (if `|T| < n − e`)
and pairwise disjoint, so there are at most `n − |T| ≤ 2e` good points.

The two regimes are **incomparable** and both are recorded: `δ < (1 − ρ)/3` here versus
`δ < (1 − √ρ)/2` in §28.3.  For `ρ = 1/2` (`1/6` vs `≈ 0.1047`) and `ρ = 1/4` (`1/4` vs
`≈ 0.2205`) this section is stronger, both in radius and in the constant; for `ρ = 1/8` and
`ρ = 1/16` the Johnson-type route of §28.3 reaches a larger radius.

### 28.5 Numerical pre-verification (`analysis/`)

| script | what it checks |
| --- | --- |
| `analysis/gs_dimension_check.py` | for many small `(n,k,m)`, that the monomial count `#{(a,b) : a + k b < L}` exceeds the constraint count `n·C(m+1,2)` exactly when the Lean hypothesis `k·n·(m+1) < m·t²` (with `L = m·t`) holds; no discrepancy found |
| `analysis/mca_small_field_check.py` | brute-force over small fields (`q ≤ 13`), small `n,k,e`: for every line `f₀ + z f₁`, the number of good `z` and of bad `z`, compared against the proved bounds `#bad ≤ 2e+1` and `#bad ≤ n·Λ`; no counterexample found |
| `analysis/mca_constants_check.py` | the concrete constants of §28.3–28.4: for `ρ ∈ {1/2,1/4,1/8,1/16}`, `n = 2²⁰`, `m = 4`, the admissible radius `e`, the bound `B` on `n·m·t/k`, and the exact field size needed for `2⁻¹²⁸` |

The field sizes are worth stating plainly: with an error bound of order `n/|F|` and `n = 2²⁰`,
**no** field of size `2⁶⁴` can give `2⁻¹²⁸`; the requirement is `|F| ≥ 2¹⁴⁷`–`2¹⁵³` for the
parameter sets above.  This is a property of the bound shape `Θ(n/|F|)`, not an artefact of the
formalisation.

## 29. Mutual correlated agreement without Hensel lifting

This section records the four routes that were pursued in place of the discriminant /
Hensel-lifting machinery of BCIKS20 §5: the syndrome-space lens, the strict-gap rigidity it
yields, the capacity barrier, and the circuit-incidence bound.  All statements are proved in
Lean and audited in `RequestProject/Main.lean`; only `propext`, `Classical.choice` and
`Quot.sound` occur.

### 29.1 The syndrome-space lens (`Root/CodingTheory/SyndromeSpace.lean`)

The lens is set up abstractly first, for an arbitrary linear "syndrome" map
`syn : (ι → F) →ₗ[F] W`, and only then specialised to Reed–Solomon codes with
`rsSyndrome k = Submodule.mkQ (reedSolomonCode F D k)`.

| statement | Lean name |
| --- | --- |
| words supported on `T` form a submodule; membership and Hamming-weight bound | `Syndrome.supportedSubmodule`, `Syndrome.mem_supportedSubmodule`, `Syndrome.hammingWeight_le_of_mem_supported` |
| the syndrome space of radius `E`, and its monotonicity in `E` | `Syndrome.syndromeSpace`, `Syndrome.syndromeSpace_mono` |
| `syn y ∈ syndromeSpace E ↔ y is within Hamming distance E of ker syn` | `Syndrome.mem_syndromeSpace_iff` |
| the column span `U_T` of a support `T`, and `syn y ∈ U_T ↔ y agrees with an element of ker syn outside T` | `Syndrome.supportSpan`, `Syndrome.mem_supportSpan_iff` |
| affine syndrome line `s(z) = A + z·B` | `Syndrome.syndromeLine` |
| **trapped line**: two distinct incidences with a subspace trap the whole line | `Syndrome.syndromeLine_trapped` |
| dichotomy: an affine syndrome line meets a subspace in at most one point, or entirely | `Syndrome.syndromeLine_dichotomy` |
| RS specialisation: the syndrome map, its kernel and its linearity along a line | `rsSyndrome`, `ker_rsSyndrome`, `rsSyndrome_lineComb` |
| `rsSyndrome y ∈ U_T ↔ IsCloseOn k (Dᶜ ∖ T) y` | `mem_supportSpan_iff_isCloseOn` |
| **`proximity_iff_syndrome`**: `distToCode k y ≤ E ↔ rsSyndrome k y ∈ syndromeSpace E` | `proximity_iff_syndrome` |
| **small-union rigidity**: two distinct points of a line close on the *same* `S` ⇒ the whole line is | `lineCloseOn_of_two_close_on` |
| interpolation on `≤ k` positions; hence `distToCode k y ≤ n − k` for every `y` | `exists_poly_agree_on_of_card_le`, `distToCode_le_card_sub` |
| **vacuity at capacity**: at radius `e = n − k` every point of every line is "close" | `capacity_premise_vacuous` |
| MDS input: `U_T = ⊤` as soon as `|T| ≥ n − k` | `supportSpan_eq_top` |
| RS dimension `= k` for `k ≤ n`, and existence of a parity-check matrix of `n − k` rows | `finrank_reedSolomonCode`, `exists_parityCheckMatrix` |

### 29.2 Strict-gap rigidity (`Root/CodingTheory/SyndromeRigidity.lean`)

The geometric picture of §29.1 sharpens the counting of §28.4: instead of `2e + 2` good
points, `e + 2` suffice.

| statement | Lean name |
| --- | --- |
| `1 ≤ k`, `k + 3e ≤ n`, `e + 2 ≤ #good(z)` ⇒ one pair `(q₀,q₁)` agrees with `(f₀,f₁)` on `≥ n − e` positions | `correlatedAgreement_of_card_goodZ_ge` |
| **`#bad ≤ e + 1`** whenever `1 ≤ k` and `k + 3e ≤ n` | `card_badSet_le_succ` |
| `ε_mca ≤ (e + 1)/|F|`, per line and for the worst line | `epsMCA_le_succ`, `epsMCAmax_le_succ` |

This is a factor-two improvement on `epsMCAmax_le_third` (`(2e+1)/|F|`) in the same regime.

### 29.3 The capacity barrier (`Root/CodingTheory/CapacityBarrier.lean`)

Correlated agreement is not merely unproved above the capacity radius `e = n − k`: it is
**false** there.

| statement | Lean name |
| --- | --- |
| under `C(n, n−k−1) < |F|²` there is a line no `(k+1)`-subset of which works, although every point is `(n−k)`-close | `exists_no_correlatedAgreement_at_capacity` |
| every line is trivially close on every set of `≤ k` positions | `lineCloseOn_of_card_le` |
| the sharp form: vacuous premise, tautological conclusion below `k+1`, failure above | `capacity_agreement_sharp` |
| a non-vacuous instance over `𝔽₅` with `n = 5`, `k = 2` | `capacity_agreement_sharp_zmod5` |

The counting hypothesis `C(n, n−k−1) < |F|²` is restrictive — it holds for short domains over
large fields and fails at FRI scale; this is recorded in `DISCREPANCIES.md`.

### 29.4 The circuit-incidence bound (`Root/CodingTheory/CircuitIncidence.lean`)

An **unconditional** bound on the number of bad parameters, valid at *every* error budget —
in particular strictly beyond the Johnson radius, where §28 and §29.2 say nothing.

| statement | Lean name |
| --- | --- |
| generalised RS closeness `w = v·p` on `A` with `deg p < k`, and the `v ≡ 1` case | `GrsCloseOn`, `grsCloseOn_one_iff` |
| interpolation and uniqueness for generalised RS codewords | `grsCloseOn_of_card_le`, `eq_of_grsCloseOn` |
| **shortening at one coordinate**: `GrsCloseOn v k (insert x B) w ↔ GrsCloseOn (v·(·−x)) (k−1) B (w − v·w(x)/v(x))` | `grsCloseOn_insert_iff` |
| **rejecting-test abundance**: `¬GrsCloseOn v k S w` ⇒ at least `C(|S|−1, a−1)` of the `a`-subsets of `S` reject, for every `k+1 ≤ a ≤ |S|` | `card_rejectingSets_ge` |
| **direction criterion**: a witness set of a bad parameter rejects the direction vector `f₁` | `not_isCloseOn_snd_of_witness` |
| **circuit-incidence bound**: `#bad · C(T−1, a−1) ≤ C(n, a)` with `T = max(n − e, k+1)` and `k+1 ≤ a ≤ T` | `card_badSet_le_circuit` |
| the corresponding bound on `ε_mca`, per line and for the worst line | `epsMCA_le_circuit`, `epsMCAmax_le_circuit` |
| **unconditional corollary**: `#bad ≤ C(n, k+1)` and `ε_mca ≤ C(n, k+1)/|F|` at *every* error budget | `card_badSet_le_choose`, `epsMCAmax_le_choose` |
| **knife edge (`Δ = 1`)**: at `e = n − (k+1)` a single incidence carries no information — an explicit line with a bad parameter | `exists_isBad_knife_edge` |
| concrete post-Johnson instance: `n = 64`, `k = 16` (`ρ = 1/4`, Johnson radius `1/2`), `e = 40` (`δ = 0.625`) ⇒ `ε_mca ≤ 2³³/|F|` | `epsMCAmax_le_circuit_64_16_40` |

The proof of the abundance lemma is a strong induction on `|S|`.  Deleting a coordinate `x`
either preserves the rejection — and the inductive count on `S ∖ {x}` applies — or it does
not, in which case *every* `a`-set through `x` rejects; in the first case the tests through
`x` are counted by the same lemma for the shortened code of one lower dimension, and the two
counts add up by Pascal's rule.  The disjointness step uses `lineCloseOn_of_two_close_on` of
§29.1: if two distinct bad parameters owned the same rejecting set `A`, the whole line — and
hence `f₁` — would be close on `A`.

### 29.4a The rank-margin trichotomy, leg by leg

With `Δ = t − k = (n − e) − k` the rank margin of the witness sets, the three legs of the
trichotomy of ePrint 2025/1712 are covered as follows.

| leg | what is proved here | Lean name |
| --- | --- | --- |
| `Δ = 0` (capacity, `e = n − k`) | the premise is vacuous — every point of every line is `(n−k)`-close — and correlated agreement genuinely **fails** above the radius | `capacity_premise_vacuous`, `capacity_agreement_sharp` |
| `Δ = 1` (knife edge, `e = n − k − 1`) | unconditional rigidity **fails**: an explicit line, and a witness set of exactly the required size, on which one point of the line is a codeword while the line is not | `exists_isBad_knife_edge` |
| `Δ ≥ 2` (strict gap) | rigidity holds in the regime `k + 3e ≤ n`, with the sharpened count `#bad ≤ e + 1`; and *unconditionally* at every radius with the circuit-incidence count | `correlatedAgreement_of_card_goodZ_ge`, `card_badSet_le_succ`, `card_badSet_le_circuit` |

The paper's own `Δ ≥ 2` theorem is proved only under `(r+1)k < m+1`, which for the optimal
`r = 2` is exactly the unique-decoding condition `3e < n − k + 1`; see `DISCREPANCIES.md`, O23.

### 29.5 Numerical behaviour of the circuit-incidence bound

The optimal test size is always `a = k + 1`, i.e. a *circuit* of the code, and the bound is
then `C(n, k+1)/C(n−e−1, k)`.  Evaluated by `analysis/post_johnson_check.py`:

| `n` | `k` | `ρ` | Johnson radius | `e` | `δ = e/n` | `log₂` of the bound on `#bad` |
| --- | --- | --- | --- | --- | --- | --- |
| 64 | 16 | 1/4 | 0.500 | 24 | 0.375 | 15.2 |
| 64 | 16 | 1/4 | 0.500 | 32 | 0.500 | 22.1 |
| 64 | 16 | 1/4 | 0.500 | 40 | 0.625 | 32.4 |
| 64 | 16 | 1/4 | 0.500 | 44 | 0.688 | 40.4 |
| 64 | 32 | 1/2 | 0.293 | 20 | 0.312 | 28.2 |
| 128 | 32 | 1/4 | 0.500 | 64 | 0.500 | 42.1 |
| 256 | 64 | 1/4 | 0.500 | 128 | 0.500 | 82.0 |

The bound therefore stays nontrivial well past the Johnson radius, up to the capacity radius
`1 − ρ` (past which §29.3 shows correlated agreement is simply false), but its constant grows
exponentially in `k`, so at FRI scale (`n = 2²⁰`) it is vacuous.  This is stated plainly in
`DISCREPANCIES.md`.

### 29.6 Numerical pre-verification (`analysis/`)

| script | what it checks |
| --- | --- |
| `analysis/syndrome_space_check.py` | exhaustively over `q ≤ 5`, `n ≤ 4`: `proximity_iff_syndrome`, `mem_supportSpan_iff_isCloseOn`, and the trapped-line dichotomy; no discrepancy found |
| `analysis/circuit_incidence_check.py` | exhaustively over `q ≤ 5`, `n ≤ 4`: the rejecting-test abundance lemma (2.5 M instances) and the circuit-incidence inequality for every line; no discrepancy found, and the bound is tight on those instances |
| `analysis/post_johnson_check.py` | evaluates the proved bound for a range of rates and budgets and reports the optimal test size (always `a = k+1`) |

## 30. A pair covering of the bad set: radius `1 − (ρ(1+1/m))^{1/4}` (`SetFamilyJohnson.lean`, `MCAPairCover.lean`)

`MCAJohnson.lean` / `MCAJohnsonGS.lean` bound the bad set of a line by producing **one**
correlated-agreement pair `(q₀,q₁)` for the whole line; that needs two witnesses to overlap
in `≥ n − 2e` positions and therefore stops at *half* the Johnson radius.  Replacing the
single pair by a **family** of pairs pushes the radius up, still unconditionally.

| statement | Lean name |
| --- | --- |
| abstract Johnson bound for set families: if `#S i ≥ t` for all `i` and `#(S i ∩ S j) ≤ c` for `i ≠ j`, then `#A · (t² − N·c) ≤ N·t` on a ground set of size `N` | `card_family_le_of_pairwise_inter` |
| fibre bound: at most `n` bad parameters can share one correlated-agreement pair `(q₀,q₁)` | `card_le_of_common_pair` |
| **pair covering**: `#bad ≤ n·Λ(k,τ)² + (Johnson term)` for every threshold `τ` | `card_badSet_le_pairCover` |
| the resulting bounds on `ε_mca` | `epsMCA_le_pairCover`, `epsMCAmax_le_pairCover` |
| with the Guruswami–Sudan list size substituted (explicit constants) | `epsMCAmax_le_pairCover_gs` |

The radius reached is `δ < 1 − (ρ·(1 + 1/m))^{1/4}` — better than the half-Johnson radius at
low rate, worse than the Johnson radius itself.  It is unconditional: no hypothesis beyond
the arithmetic side conditions appears.

## 31. Path 2: mutual correlated agreement from the discriminant of the formal line

The route asked for in the "resultant/discriminant" work package: Guruswami–Sudan
interpolation on the **formal line** `f₀ + Z·f₁`, then `Res_Y(Q, ∂_Y Q)` as a polynomial in
the line parameter `Z`, whose roots contain every bad parameter.  No Hensel lifting, no
function fields.

### 31.1 The fourth theoretical root: `Root/MultivariateResultant.lean`

Application-independent material about resultants of polynomials over a *polynomial*
coefficient ring, with formal degrees.

| statement | Lean name |
| --- | --- |
| degree of a determinant: `deg det M ≤ Σᵢ maxⱼ deg Mᵢⱼ` (in the coefficient-degree grading) | `natDegree_det_le` |
| degree of the entries of the Sylvester matrix | `natDegree_sylvester_entry_le` |
| **degree of a resultant**: `deg_Z Res(f,g,dF,dG) ≤ dG·d(f) + dF·d(g)` when all coefficients have `Z`-degree `≤ d` | `natDegree_resultant_le` |
| formal-degree discriminant `discRes B f = Res(f, f′, B, B−1)` and its behaviour under a ring map | `discRes`, `discRes_map` |
| degree bound for the discriminant | `natDegree_discRes_le` |
| a common linear factor kills the resultant; a square factor kills the discriminant | `resultant_eq_zero_of_common_linear_factor`, `discRes_eq_zero_of_sq_dvd` |
| translation bookkeeping (`eval`, `taylor`) for the degree estimates | `natDegree_eval_le`, `natDegree_coeff_taylor_le`, `natDegree_coeff_coeff_taylor_le` |

### 31.2 Interpolation on the formal line (`TrivariateInterpolation.lean`)

"Trivariate" is modelled as the iterated polynomial ring `(F[Z])[X][Y]`, so that the
bivariate Guruswami–Sudan layer of `MultivariateInterpolation.lean` — which was generalised
in this pass to an arbitrary commutative coefficient ring — applies verbatim with `R = F[Z]`,
and specialising `Z := z` is `Polynomial.map`.

| statement | Lean name |
| --- | --- |
| `Z`-degree predicate, specialisation, the formal line word `f₀ x + Z·f₁ x` | `ZdegLe`, `specZ`, `lineVal` |
| the `Z`-degree of a translated coefficient grows by at most `deg_Y Q` | `zdegLe_shiftBiv` |
| specialising `Z` preserves multiplicities and the weighted degree | `hasMultAt_specZ`, `wdegLt_specZ` |
| **interpolation on the formal line**: a nonzero `Q` with `wdeg < L`, `deg_Z ≤ dZ`, `deg_Y ≤ bY`, multiplicity `≥ m` at every `(x, f₀x + Z f₁x)`, as soon as `n·C(m+1,2)·(dZ+bY+1) < #monIdx(k,L)·(dZ+1)` | `exists_line_interpolating` |
| the **double-root lemma**: agreement on `A` with `L ≤ m·#A` *and* `L' ≤ (m−1)·#A`, `L ≤ L'+k`, gives `(Y − p)² ∣ Q_z` | `GS.sq_dvd_of_agreement` |

The number of unknowns is multiplied by `dZ + 1` while the number of conditions is
multiplied by only `dZ + bY + 1`; so a *fixed* margin in the usual Guruswami–Sudan count
already suffices, for a `dZ` that does not grow with `n`.

### 31.3 Containment and the bad-set bound (`DiscriminantMCA.lean`)

| statement | Lean name |
| --- | --- |
| the discriminant of the line at an evaluation point `x₀`: `discLine bY x₀ Q = discRes bY (Q(x₀,·,·))` | `discLine` |
| specialisation commutes: `(discLine bY x₀ Q).eval z = discRes bY ((Q_z)(x₀,·))` | `eval_discLine` |
| **containment**: an agreeing `z` is a root of the discriminant | `eval_discLine_eq_zero_of_agreement`, `eval_discLine_eq_zero_of_isBad` |
| existence of the interpolation data for a line | `exists_lineInterpolant` |
| `#bad ≤ deg discLine` and the **degree bound** `deg_Z discLine ≤ (bY + (bY−1))·dZ` | `card_badSet_le_natDegree_discLine`, `natDegree_discLine_le` |
| **`#bad ≤ (2bY − 1)·dZ`** — a bound that does *not* grow with `n` | `card_badSet_le_disc` |
| the resulting bounds on `ε_mca` | `epsMCA_le_disc`, `epsMCAmax_le_disc` |
| the same with the counting condition in clean integer form | `epsMCAmax_le_disc_clean` |

### 31.4 Concrete `2⁻¹²⁸` thresholds (`ThresholdDiscriminant.lean`)

`n = 2²⁰`, `η = 2⁻¹⁰`, radius `1 − √ρ − η`, parameters found by the exact integer search of
`analysis/threshold_discriminant_check.py`:

| `ρ` | `k` | `e` | `t` | `m` | `L` | `bY` | `dZ` | `#bad ≤` | Lean name |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 524288 | 306096 | 742480 | 866 | 642769488 | 1225 | 1317272 | 3225999128 | `threshold_rho_half_discriminant` |
| 1/4 | 262144 | 523263 | 525313 | 768 | 403177215 | 1537 | 1181574 | 3630976902 | `threshold_rho_quarter_discriminant` |
| 1/8 | 131072 | 676824 | 371752 | 624 | 231732568 | 1767 | 958721 | 3387161293 | `threshold_rho_eighth_discriminant` |
| 1/16 | 65536 | 785407 | 263169 | 481 | 126386656 | 1928 | 739707 | 2851570485 | `threshold_rho_sixteenth_discriminant` |

In all four cases `#bad ≤ 2³²`, so `|F| ≥ 2¹⁶⁰` gives `ε_mca ≤ 2⁻¹²⁸`.  That the stated `e`
really is (at most) `n·(1 − √ρ − 2⁻¹⁰)` is proved separately in
`radius_rho_half`, `radius_rho_quarter`, `radius_rho_eighth`, `radius_rho_sixteenth`.

### 31.5 The Johnson-regime bound `C·n²/|F|` (`JohnsonDiscriminant.lean`)

| statement | Lean name |
| --- | --- |
| the parameter schedule `L = (m−1)t + k`, `bY = (L−1)/k`, `dZ = k·n·m(m+1)(bY+1)`, `C = 2m²B(m+1)(mB+1)` | `johnsonL`, `johnsonBY`, `johnsonDZ`, `johnsonC` |
| **integer form**: from the margin `k·n·m(m+1) < L²` alone, `ε_mca ≤ C·n²/\|F\|` | `epsMCAmax_le_johnson_nat` |
| the multiplicity rule `m = max(4, ⌈2√ρ/η⌉ + 1)` and the inverse rate `B = ⌈2/ρ⌉` | `johnsonM`, `johnsonB` |
| **the margin holds** at radius `1 − √ρ − η` | `johnson_margin` |
| **the Johnson-regime bound**: `e ≤ n(1 − √ρ − η)`, `k ≤ ρn ≤ 2k` ⇒ `ε_mca ≤ C(ρ,η)·n²/\|F\|` | `epsMCAmax_le_johnson_disc` |
| the same in `∃ C` shape | `exists_const_epsMCAmax_le_johnson` |

**Standing hypothesis.**  Every statement of §31.3–31.5 carries the non-degeneracy
hypothesis that some evaluation point `x₀` makes the discriminant of the interpolant a
nonzero polynomial in `Z`.  It cannot be dropped — see `DISCREPANCIES.md`, A5 and O29 — and
it is the one piece of the argument that is assumed rather than proved.

**A checkable criterion for it.**  The hypothesis is now reduced to squarefreeness in `Y`:
if at the point `x₀` the specialised interpolant `Q(x₀, Y, Z) ∈ F[Z][Y]` has `Y`-degree
exactly `bY`, its `Y`-derivative has `Y`-degree exactly `bY − 1`, and the two are coprime,
then the discriminant is a nonzero polynomial in `Z`
(`Root.MultivariateResultant.discRes_ne_zero_of_isCoprime`, and its specialisation
`Root.CodingTheory.discLine_ne_zero_of_isCoprime`).  This does not *prove* A5 — coprimality
is itself a genericity statement — but it replaces "the resultant is nonzero" by the more
familiar "the fibre polynomial is squarefree".

### 31.6 Numerical pre-verification (`analysis/`)

| script | what it checks |
| --- | --- |
| `analysis/discriminant_path_check.py` | brute force over `p ≤ 13`: the double-root property and the containment `bad ⊆ roots(disc)`; also reports the degenerate (identically-zero discriminant) instances |
| `analysis/discriminant_containment_check.py` | 93 non-degenerate instances satisfying both margin conditions: 0 containment failures.  Control group where only the *simple*-root condition holds: **43 containment failures out of 107** — the double-root condition is genuinely necessary |
| `analysis/discriminant_degree_check.py` | 240 interpolants: `deg_Z Q ≤ dZ`, `deg_Y Q ≤ bY`, `wdeg Q < L`, `deg_Z Res_Y ≤ (2bY−1)dZ`; 45772 instances of the implication "clean counting condition ⇒ monomial counting condition"; 5347 instances of the Johnson schedule and 171 `(ρ,η,n)` triples for the multiplicity rule |
| `analysis/threshold_discriminant_check.py` | the exact integer search producing the four parameter sets of §31.4 |

## 32. Path 2 closed — negatively: the discriminant route is degenerate (`DiscriminantDegeneracy.lean`)

The whole of §31 is conditional on the non-degeneracy hypothesis (A5)

  `(ND)  ∀ f₀ f₁ Q, LineInterpolant k L m bY dZ D f₀ f₁ Q → ∃ x₀, discLine bY x₀ Q ≠ 0`.

This section settles (ND): **it is false**, for every parameter schedule of the route in
which an interpolant exists at all.  Consequently the conditional theorems of §31 are
vacuous, and the perturbation programme `Q ↦ Q + t·M` cannot repair them.

### 32.1 The structure theorem

Take the line `f₀ = f₁ = 0`, which lies inside the code.  Writing `Q = Σ_j c_j(X, Z)·Y^j`,
the multiplicity conditions at `(x, 0)` for all `x ∈ D` say exactly that `(X − x)^{m−j}`
divides `c_j` for every `x ∈ D`, so a nonzero `c_j` has `X`-degree at least `(m − j)·n`,
whereas the weighted-degree budget forces `deg_X c_j + k·j < L`.  Hence

  `c_j = 0`   whenever  `(m − j)·n + k·j ≥ L`,

i.e. `Y^{j₀} ∣ Q` with `j₀ = min {j : (m − j)·n + k·j < L}`.

| statement | Lean name |
| --- | --- |
| a nonzero `P ∈ F[X]` of degree `< |F|` has a non-root (the requested non-vanishing lemma) | `exists_eval_ne_zero` |
| divisibility by `(X − x)^r` at `\|D\|` points forces `deg ≥ r·\|D\|` | `natDegree_ge_of_forall_pow_dvd` |
| the multiplicity condition at `(x,0)` is divisibility of the `Y`-coefficients | `pow_dvd_coeff_of_hasMultAt_zero` |
| **structure theorem**: `c_j = 0` when `L ≤ (m−j)·\|D\| + k·j` | `coeff_eq_zero_of_zeroLine` |
| `Y² ∣ Q` when `L ≤ m·\|D\|` and `L ≤ (m−1)·\|D\| + k` | `X_sq_dvd_of_zeroLine` |
| `Y² ∣ Q` ⇒ the discriminant vanishes identically, at every `x₀` | `discLine_eq_zero_of_X_sq_dvd` |
| **every interpolant of the zero line is degenerate** | `discLine_eq_zero_of_zeroLine` |

### 32.2 The refutation

| statement | Lean name |
| --- | --- |
| **(ND) is false** whenever an interpolant exists and `L ≤ m·n`, `L ≤ (m−1)·n + k` | `nondegeneracy_hypothesis_false` |
| no perturbation `Q₀ + t·M` inside the solution space helps | `perturbation_does_not_help` |
| the hypothesis of `epsMCAmax_le_johnson_disc` is unsatisfiable (whole Johnson schedule) | `johnson_nondegeneracy_false` |
| the hypotheses of the four concrete `2⁻¹²⁸` thresholds of §31.4 are unsatisfiable | `nondegeneracy_false_rho_half`, `nondegeneracy_false_rho_quarter`, `nondegeneracy_false_rho_eighth`, `nondegeneracy_false_rho_sixteenth` |

Both budget inequalities hold identically in the schedule of §31.5 (`L = (m−1)(n−e) + k`,
so `L ≤ (m−1)n + k` always and `L ≤ m·n` as soon as `k ≤ n`), which is why the refutation
covers the whole route rather than isolated parameter choices.  For the four concrete sets
the forced vanishing order is `j₀ = 507, 512, 461, 385` respectively — very far from the
borderline `j₀ = 2`.

Why the perturbation programme cannot work: the interpolation conditions are linear and
homogeneous, so any `M` for which `Q₀ + t·M` is still an interpolant keeps the perturbed
polynomial inside the same solution space `V(f₀,f₁)`, and for a line inside the code every
element of `V` is degenerate.  The non-vanishing lemma `exists_eval_ne_zero` is proved and
available, but has nothing to act on: the discriminant is identically zero in `t`.

### 32.3 What survives unconditionally

| bound | regime | Lean name |
| --- | --- | --- |
| `ε_mca ≤ C(n, k+1)/\|F\|` | every error budget | `epsMCAmax_le_choose` (§29) |
| `ε_mca ≤ (2e+1)/\|F\|` | `k + 3e ≤ n` | `epsMCAmax_le_third` (§28) |
| `ε_mca ≤ n·C(ρ,δ,m)/\|F\|` | `2δ + (1 + 1/(2m))√ρ < 1` | `epsMCAmax_le_gs_relative` (§28) |
| **`ε_mca ≤ C·n²/\|F\|`** (the shape requested for the "final" theorem) | `2δ + √ρ < 1` | `exists_const_epsMCAmax_le_sq` |

`exists_const_epsMCAmax_le_sq` is the honest unconditional replacement of the requested
`epsMCAmax_le_johnson_disc_final`: the shape is the requested one, the radius is the
half-Johnson radius rather than the full Johnson radius.  The full Johnson radius remains
open (O20, O21); §32 shows that the discriminant route as set up does not reach it.

### 32.4 Numerical pre-verification

| script | what it checks |
| --- | --- |
| `analysis/perturbation_check.py` | brute-force linear algebra over `p ≤ 13`: computes the full interpolation solution space of the zero line, confirms `Y^{j₀} ∣ Q` for every member, and confirms that the discriminant vanishes at every `x₀` for every member exactly when `j₀ ≥ 2` (the `j₀ = 1` case does contain non-degenerate members) |
| `analysis/threshold_discriminant_final_check.py` | exact integer audit of the four concrete parameter sets: counting condition, bad-set bound, both budget inequalities, and `j₀` |

---

## 33. The syndrome-space root: an explicit parity-check matrix and the rank margin

File: `RequestProject/Root/SyndromeSpace.lean` (builds on the general lens in
`RequestProject/Root/CodingTheory/SyndromeSpace.lean`).  Everything below is unconditional;
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.

### 33.1 The parity-check matrix

The dual of `RS_{<k}(D)` is a *generalised* Reed–Solomon code, so the plain Vandermonde
matrix `x ↦ x^i` is **not** a parity check (DISCREPANCIES.md, O34; the failure is exhibited
numerically over `𝔽₅`, `𝔽₇`, `𝔽₁₁`).  The correct matrix uses the GRS multipliers.

| statement | Lean name |
| --- | --- |
| `v_x = (∏_{y ∈ D∖{x}} (x − y))⁻¹` is the leading coefficient of the Lagrange basis polynomial | `leadingCoeff_lagrange_basis` |
| **Lagrange coefficient identity** `∑_{x ∈ D} f(x)·v_x = coeff_{n−1} f` for `deg f < n` | `sum_eval_mul_grsMultiplier` |
| `H i x = v_x·x^i`, `0 ≤ i < n − k` | `rsParityCheck`, `rsSyndromeMatrix` |
| `i`-th syndrome coordinate `= coeff_{n−1}(X^i·f)` for any interpolant `f` of `y` | `rsSyndromeMatrix_apply_eq_coeff` |
| **`H` is a parity-check matrix**: `ker H = RS_{<k}(D)` | `ker_rsSyndromeMatrix` |
| `dist(y, RS) ≤ E ↔ H·y ∈ syndromeSpace E` | `proximity_iff_syndrome_matrix` |

Both inclusions of `ker_rsSyndromeMatrix` come from the single identity
`sum_eval_mul_grsMultiplier`: a codeword `p` of degree `< k` gives `deg(X^i p) < n − 1`, so
every syndrome coordinate is a coefficient beyond the degree, hence zero; conversely if
`deg f ≥ k` then choosing `i = n − 1 − deg f` (legal because `i < n − k`) makes the `i`-th
coordinate equal to the leading coefficient of `f`.

### 33.2 The rank margin and the trichotomy

For an error support `T` with agreement `t = n − |T|`, the **rank margin** is
`Δ = t − k` (`rankMargin`).  The column span `U_T = H(span of words supported in T)`
satisfies:

| leg | statement | Lean name |
| --- | --- | --- |
| `Δ ≥ 0` | `dim U_T = |T|`, i.e. codim `U_T = Δ` | `finrank_supportSpan_eq_card` |
| `Δ = 0` | `U_T = F^{n−k}`: the proximity premise carries **no information** | `supportSpan_eq_top_of_margin_zero` |
| `Δ ≥ 1` | `U_T` is a proper subspace | `supportSpan_ne_top_of_margin_pos` |
| `Δ ≥ 2` | codim `U_T ≥ 2`; equivalently `\|U_T\|·\|F\|^Δ = \|F\|^{n−k}`, a density `\|F\|^{-Δ} ≤ \|F\|^{-2}` | `finrank_supportSpan_le_of_margin_ge_two`, `card_supportSpan`, `card_supportSpan_mul_pow_margin` |
| any `Δ` | two incidences trap the whole affine syndrome line | `syndromeLine_eq_of_two_mem` |

The dimension count rests on a new general lemma, `finrank_map_of_disjoint_ker`
(a linear map preserves the dimension of any submodule meeting its kernel trivially),
applied to the disjointness of the `|T|`-supported words from the code — which is exactly
the Reed–Solomon minimum-distance bound `reedSolomon_weight_ge`.

The Δ = 1 knife-edge obstruction is `exists_isBad_knife_edge` (`CircuitIncidence.lean`) and
the Δ = 0 vacuity is `capacity_premise_vacuous`/`capacity_agreement_sharp`; the Δ ≥ 2
capacity-regime rigidity claimed in the literature is **not** proved here, for the reason
recorded in O23/O36.

### 33.3 MCA below capacity

`mca_reduces_to_ca_below_capacity`: if the probability that a random point of the line
`f₀ + z·f₁` is `e`-close to the code exceeds `C(n, k+1)/|F|`, then a *single* set `S` with
`|S| ≥ n − e` works for the whole line.  The bound is unconditional in every parameter; the
requested hypothesis `e < n − k` turned out not to be needed and is kept only because it was
asked for (see O35 for why the requested `C_capacity·n²/|F|` shape is not claimed).

### 33.4 Numerical pre-verification

| script | what it checks |
| --- | --- |
| `analysis/syndrome_space_check.py` | `proximity_iff_syndrome`, `mem_supportSpan_iff_isCloseOn`, the trapped-line dichotomy (no discrepancy) |
| `analysis/syndrome_trichotomy_check.py` | kernel and rank of the GRS parity-check matrix; failure of the plain Vandermonde matrix; the Lagrange coefficient identity; all four legs of the rank-margin trichotomy over `𝔽₅`, `𝔽₇`, `𝔽₁₁` for every subset `T`; the trapping mechanism; and the two-sided vacuity at `Δ = 0` |

Every check passes; no counterexample was found to any statement that was subsequently
formalised, and the one check that *fails by design* is the plain-Vandermonde control
(item B), which is what motivated the correction O34.

## 34. Quantitative syndrome-space theorems and the additive margin law

Two new files complete the syndrome-space programme on the quantitative side:
`RequestProject/Root/CodingTheory/SyndromeQuantitative.lean` (rigidity from many successful
challenges) and `RequestProject/Root/CodingTheory/AdditiveMargin.lean` (independent
domain-separated folds).  Throughout, `n = |D|`, `k` is the code dimension, `e` the error
budget, `m = n − k` and the *strict-gap regime* is `k + 3e ≤ n`, i.e. `3e < d_min = m + 1`.

### 34.1 Vanishing differences

`vanishing_differences_three`: in the strict-gap regime, for *any* three challenges
`z₀, z₁, z₂` and any admissible error vectors `uᵢ` (weight `≤ e`, `f_{zᵢ} − uᵢ` a codeword),

```
(z₁ − z₂)·u₀ + (z₂ − z₀)·u₁ + (z₀ − z₁)·u₂ = 0   identically.
```

Equivalently: at each coordinate `x`, the error value `u_z(x)` is an **affine function of the
challenge `z`**.  The proof is two lines of syndrome geometry: the coefficients sum to zero
and are orthogonal to the challenges, so the corresponding combination of the words
`f₀ + z·f₁` vanishes and the combination of the errors is a codeword; its weight is at most
`3e < d_min`, hence it is zero.

`exists_vanishing_combination` restates this in the `λ`-form for `r + 1 ≥ 3` distinct
challenges: a nonzero `λ : Fin (r+1) → F` with `∑ᵢ λᵢ·uᵢ(x) = 0` at every `x`.

Two deviations from the instruction, both strengthenings, are recorded as O37: the side
condition is on the *error budget* (`3e < m+1`, not `(r+1)k < m+1`), and it is independent of
`r`; and the three challenges need not be distinct.

### 34.2 The global support bound

Let `G` be a set of successful challenges, `M = |G|`, and `S = ⋃_{z ∈ G} supp(u_z)` the
global error support.

* `card_filter_error_eq_zero_le_one` — a coordinate of `S` is switched *off* by at most one
  challenge (a nonzero affine function of `z` has at most one root);
* `global_support_bound` — double counting the incidences `{(x, z) : x ∈ S, u_z(x) ≠ 0}`
  from both sides gives `|S|·M ≤ M·e + |S|`, i.e. `|S| ≤ M·e/(M−1)`;
* `card_globalErrorSupport_le` — hence `|S| ≤ e` as soon as `M ≥ e + 2`.

The threshold `M ≥ e + 2` is genuinely needed, and not an artefact of the rounding: see O38
and the numerical evidence below.

### 34.3 Rigidity

`correlatedAgreement_of_many_challenges`: in the strict-gap regime, if at least `e + 2`
challenges make `f₀ + z·f₁` `e`-close to `RS_{<k}(D)`, then one single set `S` with
`|S| ≥ n − e` works for the *whole* line (`LineCloseOn k S f₀ f₁`).  The set is the
complement of the global error support.

`rigidity_rho_quarter` records the concrete rate-`1/4` instance: at `|D| = 2²⁰`, `k = 2¹⁸`
the strict-gap regime reaches the relative radius `δ = 1/4` exactly, and `2¹⁸ + 2` successful
challenges suffice.

This is the syndrome-native route to the statement proved by a different (polynomial
agreement) argument in `SyndromeRigidity.lean`; the two agree on hypotheses and radius, and
the syndrome proof makes the mechanism — affineness of the error in the challenge — explicit.

### 34.4 The additive margin law

At rate `ρ = 1/2` a single fold sits on the `Δ = 1` knife edge (`exists_isBad_knife_edge`),
so no unconditional `Δ ≥ 2` rigidity is available.  The route to a small soundness error is
therefore the **additive margin law** for independent, domain-separated folds.  The model is
pure counting: a fold is its bad-challenge set `B ⊆ F`; one round of two domain-separated
folds accepts a false claim exactly on `B₁ ×ˢ B₂ ⊆ F × F`; `s` independent rounds accept on
the corresponding product event in `(F × F)^s`, whose size is `|F|^{2s}`
(`card_rounds_space`).

* `falseAcceptProb_eq` — `Pr[FA] = ((|B₁|/|F|)·(|B₂|/|F|))^s`;
* `density_le_of_margin` — a fold of margin `Δ` (`|B|·|F|^Δ ≤ |F|`) has density `≤ |F|^{-Δ}`;
* `additive_margin_law` — `Pr[FA] ≤ (1/|F|)^{Δ₁+Δ₂}` for one round: **the margins add**;
* `additive_margin_law_rounds` — `Pr[FA] ≤ (1/|F|)^{(Δ₁+Δ₂)·s}` over `s` rounds.

### 34.5 A concrete `ρ = 1/2` soundness

`soundness_rho_half_two_folds`: for

| parameter | value |
| --- | --- |
| `n = \|D\|` | `2²⁰` |
| `k` (dimension) | `2¹⁹`, i.e. rate `ρ = 1/2` |
| `e` (error budget) | `2¹⁶`, i.e. `δ = 1/16` |
| strict gap | `k + 3e = 720896 ≤ 2²⁰` ✓ |
| `\|F\|` | `≥ 2³²` |
| folds per round | 2, domain-separated |
| rounds `s` | 5 |

the false-accept probability is at most `2^{-128}` (the proved value is `2^{-150}`).  The
per-fold input is the *unconditional* bound `#bad ≤ e + 1` of `card_badSet_le_succ`, so the
theorem has no hypothesis beyond the parameters above.  Note that the per-fold density is
`(e+1)/|F| ≤ 2^{-15}`, not `1/|F|`; this is why 5 rounds suffice and why a "`Δ = 1` per fold"
reading of the parameters would be optimistic (O39).

### 34.6 Numerical pre-verification

| script | what it checks |
| --- | --- |
| `analysis/syndrome_vanishing_check.py` | the vanishing-differences identity over `𝔽₂`, `𝔽₃`, `𝔽₅`, `𝔽₇` in the strict-gap regime (no violation), and explicit counterexamples once `k + 3e > n` |
| `analysis/syndrome_global_support_check.py` | `\|S\|·M ≤ M·e + \|S\|`; the rounding `M ≥ e+2 ⇒ \|S\| ≤ e`; the rigidity conclusion itself; and the sharpness of the threshold — in the sampled instances with `M = e + 1` over `𝔽₅` **every** one has `\|S\| > e` |
| `analysis/syndrome_additive_margin_check.py` | the product formula against exact enumeration of `(F × F)^s`; the margin law over all pairs of subsets of `𝔽₂…𝔽₇` and all admissible margins (64 350 instances, no counterexample); and the concrete `ρ = 1/2` arithmetic in exact rationals |

No counterexample was found to any statement that was subsequently formalised.

## 35. BCHKS25 Theorem 1.5 / ABF Theorem 4.12: the Johnson-regime MCA bound, repaired and sharpened (`BCHKSJohnson.lean`, `BCHKSThresholds.lean`)

BCHKS25 (Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, ePrint 2025/2055) Theorem 1.5 states, for
`C = RS[F, D, k]`, `n = |D|`, `ρ = k/n`, `ρ₊ = ρ + 1/n`, `η > 0`, `γ = 1 − √ρ₊ − η` and
`m = max ⌈√ρ₊/(2η)⌉ 3`,

  `ε_mca(C, γ) ≤ ( (2(m+½)⁵ + 3(m+½)γρ₊)/(3ρ₊^{3/2}) · n + (m+½)/√ρ₊ ) / |F| = O_ρ(n/(η⁵|F|))`.

This section reports what is now formalised on that statement.  The route is the
*discriminant* route of §31 (formal line `f₀ + Z f₁`, Guruswami–Sudan interpolation,
`Res_Y(Q, ∂_Y Q)`) — **no Hensel lifting** — with two changes.

### 35.1 The non-degeneracy hypothesis, repaired

§32 refutes the unrestricted hypothesis

  `(ND)  ∀ f₀ f₁ Q, LineInterpolant … Q → ∃ x₀, discLine bY x₀ Q ≠ 0`

by the **zero line**, whose interpolant is always divisible by `Y²`.  But the zero line —
and, more generally, every line spanned by two codewords — has an **empty bad set**
(`badSet_eq_empty_of_isCloseOn_univ`), and contributes `0` to `ε_mca`
(`epsMCA_eq_zero_of_badSet_empty`).  So the counting statements survive verbatim if (ND) is
imposed only on the lines that actually possess a bad point:

  `(ND′)  ∀ f₀ f₁, (badSet k e f₀ f₁).Nonempty → ∀ Q, LineInterpolant … Q → ∃ x₀, discLine bY x₀ Q ≠ 0`.

| statement | Lean name |
| --- | --- |
| a line without bad points has `ε = 0` | `epsMCA_eq_zero_of_badSet_empty` |
| lines of two codewords have empty bad set | `badSet_eq_empty_of_isCloseOn_univ` |
| MCA bound under (ND′) | `epsMCAmax_le_disc_of_bad` |
| the same with the counting condition (C) | `epsMCAmax_le_disc_clean_of_bad` |

The known refutation of (ND) does not apply to (ND′); whether (ND′) holds is open (O40).

### 35.2 A `Z`-degree budget that does not grow with `n`

§31 chose `dZ = k·n·m(m+1)(bY+1)`, which is legitimate but costs a factor `n²`.  The
smallest admissible budget is

  `dZ = ⌊P(bY+1)/A⌋ + 1`,   `P = k·n·m(m+1)`,   `A = L² − P`   (`bchksDZ`),

and in the Johnson regime the margin `A` is itself of order `n²`.  Taking the multiplicity
`m = max 4 (⌈4√ρ/η⌉ + 1)` (`bchksM`, twice the multiplicity of `johnsonM`) gives the
*quantitative* margin `k·n + k·n·m(m+1) ≤ L²` (`bchks_margin`), whence `A ≥ k·n` and

  `dZ ≤ m(m+1)(mB+1) + 1`,   `#bad ≤ (2bY − 1)·dZ ≤ C(ρ,η) := 2mB(m(m+1)(mB+1)+1)`,

with `B = ⌈2/ρ⌉` — **independent of `n`**.

| statement | Lean name |
| --- | --- |
| integer form (only input: the quantitative margin) | `epsMCAmax_le_bchks_nat` |
| the margin at radius `1 − √ρ − η` | `bchks_margin` |
| `ε_mca ≤ C(ρ,η)/|F|` | `epsMCAmax_le_bchks_disc` |
| the BCHKS shape `ε_mca ≤ C(ρ,η)·n/|F|` | `epsMCAmax_le_bchks_linear` |
| `∃ C` form | `exists_const_epsMCAmax_le_bchks` |

This sharpens §31's `C·n²/|F|` to `C/|F|`; both remain conditional on (ND′).

### 35.3 The concrete thresholds `2⁻¹²⁸`

`bchksRHS n ρ₊ η` is the literal right-hand side of BCHKS25 Theorem 1.5, and
`two_pow_32_le_bchksRHS` shows it is at least `2³²` whenever `n ≥ 2²⁰`, `ρ₊ ≥ 1/16` and
`η = 2⁻¹⁰`.  For `n = 2²⁰`, `η = 2⁻¹⁰` and the **exact BCHKS radius**
`e = ⌊n(1 − √ρ₊ − η)⌋` (`radius_plus_rho_*`):

| `ρ` | `k` | `e` | `m` | `L` | `bY` | `dZ` | `#bad ≤` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/2 | 524288 | 306096 | 866 | 642769488 | 1225 | 1318349 | 3228636701 ≤ 2³² |
| 1/4 | 262144 | 523263 | 768 | 403177215 | 1537 | 1182344 | 3633343112 ≤ 2³² |
| 1/8 | 131072 | 676822 | 624 | 231733814 | 1767 | 953690 | 3369386770 ≤ 2³² |
| 1/16 | 65536 | 785406 | 481 | 126387136 | 1928 | 737936 | 2844743280 ≤ 2³² |

| statement | Lean name |
| --- | --- |
| `ε_mca ≤ 2⁻¹²⁸` for `\|F\| ≥ 2¹⁶⁰` | `threshold_rho_half_bchks`, `…_quarter_…`, `…_eighth_…`, `…_sixteenth_…` |
| the literal BCHKS25 bound holds at these parameters | `epsMCAmax_le_bchksRHS_rho_half`, … |

For comparison, BCHKS25's own right-hand side at these parameters is `≈ 2⁶³`, so the paper
asks for `|F| ≳ 2¹⁹¹` where the (conditional) schedule above needs `2¹⁶⁰`; see
`analysis/bchks_threshold_check.py`.

### 35.4 Line-decodability / collinearity of proximates (`LineDecodable.lean`)

`IsLineDecodable k e a b D` is ABF §4.4 / GG25 Definition 3.1 in absolute form: for all
`u₀, u₁` and every family of codewords `f : F → C`, if
`A = {α : Δ(u₀ + α u₁, f α) ≤ e}` has `|A| ≥ a`, then `b` of the proximates are collinear,
`f α = c₀ + α c₁`.

| statement | Lean name |
| --- | --- |
| counting form of correlated agreement | `correlatedAgreement_of_card_lt` |
| a line close on `S` is spanned by two codewords on `S` | `exists_codewords_of_lineCloseOn` |
| **main theorem**: `#bad < a` and `k + 2e ≤ n` ⟹ `(e, a, a)`-line-decodable | `isLineDecodable_of_card_badSet_lt` |
| the same through `ε_mca` | `isLineDecodable_of_epsMCAmax_le` |
| unconditional, unique-decoding regime | `isLineDecodable_unique_decoding` |
| unconditional, up to **half** the Johnson radius, `a = O_{ρ,δ}(n)` | `isLineDecodable_half_johnson` |

Note `b = a`: *all* proximates of `A` are collinear, the strongest form of the definition.
The two unconditional instances are the honest state of the art here; the full Johnson
radius is reached only through §35.2, i.e. under (ND′).

### 35.5 Numerical pre-verification

| script | what it checks |
| --- | --- |
| `analysis/bchks_dimension_check.py` | for all `n ≤ 40` and all `k, e, m`: the margin `L² > k n m(m+1)` implies a positive interpolation dimension count; the closed-form condition (C) implies the true monomial count; and the sharpened `dZ` always satisfies (C) |
| `analysis/bchks_resultant_degree_check.py` | on 400 random instances over `𝔽₁₀₁`: `deg_Z Res_Y(Q, ∂_Y Q) ≤ (2bY − 1)·dZ` |
| `analysis/bchks_threshold_check.py` | the BCHKS25 right-hand side and the required field size for `2⁻¹²⁸`, against the integer schedule above, for `n = 2²⁰` and `ρ ∈ {1/2, 1/4, 1/8, 1/16}` |

No counterexample was found to any statement that was subsequently formalised.

## 36. An unconditional *lower* bound: `ε_mca = Ω(1/|F|)` (`MCALowerBound.lean`)

Sections 31–35 bound `ε_mca(C, e)` from above.  This section provides the matching
unconditional **lower** bound, so that the `1/|F|` scale of those bounds is now known to be
correct and not an artefact of the method.

### 36.1 The construction

Fix `k < |D|` and a colouring `g : D → F`, and put

  `u₁ x = xᵏ`  (`powWord`),   `u₀ x = −g(x)·xᵏ`  (`blockWord`).

The line point `u₀ + γ·u₁` is the word `x ↦ (γ − g x)·xᵏ`, which vanishes identically on the
fibre `S_γ = g⁻¹(γ)` (`lineComb_blockWord`).  Hence `S_γ` witnesses `IsCloseOn k S_γ` for the
point `γ`.  On the *same* fibre the neighbouring point `u₀ + (γ+1)·u₁` is exactly `x ↦ xᵏ`,
and `x ↦ xᵏ` agrees with no polynomial of degree `< k` on more than `k` positions
(`not_isCloseOn_powWord`, because `Xᵏ − p` is a nonzero polynomial of degree exactly `k`).
So `S_γ` refutes `LineCloseOn`, and `γ` is bad.

| statement | Lean name |
| --- | --- |
| `x ↦ xᵏ` is a codeword on no set of `> k` positions | `not_isCloseOn_powWord` |
| every fibre with `> max(\|D\|−e, k)` elements gives a bad point | `isBad_blockWord` |
| counting form | `card_le_card_badSet_blockWord` |
| `ε_mca ≥ \|Z\|/\|F\|` | `card_div_card_le_epsMCAmax` |

### 36.2 The two instances

* **Constant colouring** (`g ≡ 0`, one fibre `= D`): for every `k < |D|` and every radius `e`,

    `ε_mca(C, e) ≥ 1/|F|`   (`one_div_card_le_epsMCAmax`).

* **`r` blocks** (`modColouring`: residue classes mod `r` along an arbitrary enumeration of
  `D`, each of size `≥ ⌊|D|/r⌋`): if `r ≤ |F|` and `r·max(|D|−e, k+1) ≤ |D|`, then

    `ε_mca(C, e) ≥ r/|F|`   (`card_le_epsMCAmax_of_blocks`).

  In the Johnson regime `|D| − e ≈ √ρ·|D|`, so `r` can be taken as large as `⌊1/√ρ⌋`
  (e.g. `r = 4` at `ρ = 1/16`).

Both statements are **unconditional**: no non-degeneracy hypothesis, no interpolation, no
constraint linking `k`, `e` and the Johnson radius beyond what is displayed.

### 36.3 What this pins down

Combining with §35.2 (`epsMCAmax_le_bchks_disc`, `≤ C(ρ,η)/|F|`, conditional on (ND′)):

  `⌊1/√ρ⌋/|F| ≤ ε_mca(C, γ) ≤ C(ρ,η)/|F|`,

i.e. `ε_mca = Θ_ρ(1/|F|)` on the whole range covered by §35 — in particular the linear
factor `n` of the BCHKS25 right-hand side is *not* necessary at these parameters, while
some `Ω_ρ(1)` constant is.  The concrete `2⁻¹²⁸` thresholds of §35.3 therefore cannot be
improved below `|F| ≥ 2¹²⁸`.

### 36.4 Numerical control

`analysis/mca_lower_bound_check.py` brute-forces, over `𝔽₅, 𝔽₇, 𝔽₁₁` and all
`D = {0,…,n−1}`, `k`, `e`, `r`, that each large fibre really witnesses closeness for its own
line point and really refutes line-closeness (308 instances with a guaranteed nonempty bad
set), and that `x ↦ xᵏ` never agrees with a polynomial of degree `< k` on more than `k`
points.  No failure.

## 37. Collinearity of proximates ⟺ a formal root of the line (`FormalRoot.lean`)

The last step of the BCHKS25 / ABF argument, isolated and proved **unconditionally**.

Write the formal line as `w(x) = u₀ x + Z·u₁ x ∈ F[Z]`.  A **formal root** of the line on
`S ⊆ D` is a `p = Σ_j c_j(X)·Z^j ∈ (F[X])[Z]` with all `deg c_j < k` and

  `p(x, Z) = u₀ x + Z·u₁ x`  for every `x ∈ S`   (`IsFormalRoot`).

| statement | Lean name |
| --- | --- |
| a formal root makes **all** proximates collinear on `S` (`c₀ = p.coeff 0`, `c₁ = p.coeff 1`) | `lineCloseOn_of_formalRoot` |
| conversely, line-closeness yields a formal root of `Z`-degree `≤ 1` | `formalRoot_of_lineCloseOn` |
| **equivalence** | `lineCloseOn_iff_formalRoot` |
| rigidity: a candidate of `Z`-degree `≤ d` (`d ≥ 1`) matching the line at `> d` challenges *is* a formal root | `formalRoot_of_agreements` |
| correlated agreement from a formal root on a large set | `correlatedAgreement_of_formalRoot` |

`formalRoot_of_agreements` is the quantitative content: the formal line has `Z`-degree `1`,
so a `Z`-degree-`d` candidate that matches it at `d+1` distinct challenges is forced to be
linear in `Z`, and its two coefficients are the common codewords.  For `d = 1` this is the
classical "two good challenges" argument of §30; for general `d` it is exactly the step that
consumes the global factorisation of a Guruswami–Sudan interpolant over `F(Z)`.

Thus, in the BCHKS25 pipeline, everything *after* "the interpolant has a linear-in-`Y`
factor over `F(Z)` that agrees with the line on many positions" is now formalised
unconditionally; what remains conditional (O40/O41) is the production of that factor.

## 38. The alphabet-generic MCA layer, folded Reed–Solomon codes, subspace design and curve-decodability

This section covers five new modules.  Everything in them is unconditional and `sorry`-free.

### 38.1 `Root/CodingTheory/AlphabetMCA.lean` — MCA over an arbitrary alphabet

The ambient data is: a finite field `F` (the challenges are *always* drawn from `F`), a
finite index type `ι` of positions, an alphabet `A` that is an `F`-module with decidable
equality, and an arbitrary `F`-linear code `C : Submodule F (ι → A)`.  The Hamming layer of
`Root/CodingTheory/Hamming.lean` is already alphabet-generic and is reused verbatim.

Definitions: `Alphabet.lineComb`, `Alphabet.AgreeOn`, `Alphabet.LineAgreeOn`,
`Alphabet.CloseTo`, `Alphabet.IsBad`, `Alphabet.badSet`, `Alphabet.goodZ`,
`Alphabet.epsMCA`, `Alphabet.epsMCAmax`, `Alphabet.MinDistGe`.

Theorems:

* `Alphabet.line_closure` — line closure, from the submodule structure alone;
* `Alphabet.closeTo_of_agreeOn`, `Alphabet.agreeOn_of_closeTo`, `Alphabet.mem_goodZ_of_isBad`;
* `Alphabet.correlatedAgreement_of_epsMCA_lt` — MCA ⇒ correlated agreement;
* `Alphabet.correlatedAgreement_of_two` — two successful challenges give a pair of codewords
  agreeing with `(f₀,f₁)` on `≥ n − 2e` positions (the `(γ−γ′)⁻¹` construction);
* `Alphabet.eq_lineComb_of_close`, `Alphabet.card_agreement_lineComb_ge`,
  `Alphabet.card_inter_agreement_ge` — the counting chain;
* `Alphabet.card_badSet_le` — **the unique-decoding row for an arbitrary alphabet and an
  arbitrary linear code**: `MinDistGe C d` and `3e < d` imply `#bad ≤ n`;
* `Alphabet.epsMCA_le`, `Alphabet.epsMCAmax_le` — hence `ε_mca ≤ n/|F|`.

### 38.2 `Root/CodingTheory/AlphabetInstances.lean` — the ordinary case `A = F`

`agreeOn_iff_isCloseOn`, `lineAgreeOn_iff_lineCloseOn`, `isBad_iff`, `badSet_eq`,
`epsMCA_eq` show that the generic definitions specialise *literally* to the ordinary
Reed–Solomon definitions of `MCA.lean`; `reedSolomon_minDistGe` supplies the Singleton
distance, and `epsMCA_rs_le_of_alphabet` re-derives the ordinary bound `ε_mca ≤ |D|/|F|`
through the generic layer.  So no MCA theory is duplicated for the folded case.

### 38.3 `Root/CodingTheory/FoldedRS.lean` — the folded code

`foldedEval`, `foldedEvalLT`, `foldedRSCode B k s γ : Submodule F (↥B → Fin s → F)`, the
unfolded domain `unfoldedDomain B s γ` and the folding hypothesis `IsFoldingDomain B s γ`
(the `s·|B|` points `γ^i x` are pairwise distinct), with the sufficient criterion
`isFoldingDomain_of_cosets` (γ of order ≥ s, `0 ∉ B`, distinct `⟨γ⟩`-cosets).

* `card_unfoldedDomain` — `|unfolded| = s·|B|`;
* `card_blocks_mul_le` — a nonzero polynomial of degree `< k` vanishes on at most
  `⌊(k−1)/s⌋` whole blocks;
* `card_agreement_mul_le`, `foldedRS_minDistGe` — the **block minimum distance**:
  `d ≥ |B| − ⌊(k−1)/s⌋`, i.e. relative distance `≥ 1 − ρ` up to rounding;
* `foldedEvalLT_injective`, `finrank_foldedRSCode` — dimension exactly `k`, so the rate is
  `k/(s|B|)`, the same as the ordinary code it is folded from.

### 38.4 `Root/CodingTheory/FoldedMCA.lean` — MCA for the folded code

Instantiating 38.1 at 38.3: `card_badSet_folded_le`, `epsMCA_folded_le`,
`epsMCAmax_folded_le`, `correlatedAgreement_folded` — in the regime
`3e < |B| − ⌊(k−1)/s⌋` at most `|B|` challenges are bad, so `ε_mca ≤ |B|/|F|`.
`soundness_folded_two_folds` is a concrete instance: `|B| = 2¹⁶` blocks of size `s = 16`
(unfolded length `2²⁰`), `k = 2¹⁹` (rate `1/2`), block error budget `2¹²`, `|F| ≥ 2³²`,
four rounds of two domain-separated folds give false-accept probability `≤ 2⁻¹²⁸`.

This is a *unique-decoding* radius, not a capacity radius; see `DISCREPANCIES.md` O44–O47.

### 38.5 `SubspaceDesign.lean` and `CurveDecodability.lean`

* `Alphabet.coordKer`, `Alphabet.IsSubspaceDesign C τ` — the GG25 design inequality
  `∑_i dim(H ∩ C_i) ≤ τ(r)·dim H·n`;
* `Alphabet.isSubspaceDesign_one` — the trivial design `τ ≡ 1`;
* `Alphabet.finrank_span_inf_coordKer`, `Alphabet.sum_finrank_span_inf_coordKer` — for a line
  the design sum is the number of zero coordinates;
* `Folded.foldedRS_design_dim_one` — **the `r = 1` case for folded RS with the sharp
  constant `⌊(k−1)/s⌋`**;
* `Alphabet.CurveDecodable`, `Alphabet.badSet_eq_empty_of_mem`,
  `Alphabet.card_badSet_le_card_goodZ`, `Alphabet.card_badSet_le_of_curveDecodable`,
  `Alphabet.curveDecodable_implies_mca`, `Alphabet.curveDecodable_implies_mcamax` —
  **curve-decodability implies MCA over an arbitrary alphabet**, with the trivial instance
  `curveDecodable_card` (`a = |F|`) showing the definition is not vacuous;
* `Alphabet.falseAcceptProb_le_of_margins`, `Alphabet.falseAcceptProb_le_of_curveDecodable`
  — the additive margin law of §34 applies verbatim to the generic bad sets, over two
  possibly different codes with two possibly different alphabets: the margins add.

### 38.6 Numerical pre-verification

* `analysis/linear_alphabet_mca_check.py` — for `q ∈ {5,7,11,13}`, `s ≤ 5`, `k ≤ 3`:
  the folding hypothesis, the block minimum distance, the `r = 1` design bound, the
  unique-decoding MCA bound `#bad ≤ |B|` on random and structured lines, `badSet ⊆ goodZ`,
  the emptiness of the bad set for lines inside the code, and the product form of the
  two-fold false-accept probability.  All pass.
* `analysis/subspace_design_check.py` — exhaustive enumeration of all subspaces of dimension
  `r = 1, 2` of the folded code on eight instances, comparing the design sum with the proved
  `r = 1` bound and with the GG25 shape `τ(r) = sρ/(s−r+1)` (exact rational comparisons
  discharged with Z3).  No violation found.

These scripts are exploratory pre-verification; the verified claims are the Lean theorems.

## 39. A general-`r` subspace-design bound by double counting

`RequestProject/Root/CodingTheory/SubspaceDesignGeneric.lean` adds the first design
statement of the project that is valid for **every** dimension `r`, not just `r = 1`:

* `Alphabet.finrank_lt_natCard` — a finite `F`-space has `|V| = q^{dim V} > dim V`;
* `Alphabet.sum_finrank_inf_coordKer_le` — if every nonzero word of a subspace `W` of the
  ambient space vanishes in at most `t` coordinates, then
  `Σ_i dim (W ∩ C_i) ≤ (|W| − 1)·t`.  The proof is a double count: `dim (W ∩ C_i)` is at
  most the number of *nonzero* words of `W` vanishing at `i`, and summing that over `i` is
  the same as summing, over the nonzero words `c ∈ W`, the number of coordinates where `c`
  vanishes, each of which is at most `t`;
* `Alphabet.sum_finrank_inf_coordKer_le_pow` — the same with `|W| ≤ q^r` for `dim W ≤ r`;
* `Alphabet.isSubspaceDesign_of_zero_coords_le` — hence `IsSubspaceDesign C τ` holds with
  `τ(r) = (q^r − 1)·t/n`;
* `Folded.card_zero_blocks_le` — a nonzero folded Reed–Solomon codeword vanishes on at most
  `⌊(k−1)/s⌋` blocks;
* `Folded.foldedRS_design_general` — for every subspace `W` of the folded Reed–Solomon code
  with `dim W ≤ r`, `Σ_i dim (W ∩ C_i) ≤ (q^r − 1)·⌊(k−1)/s⌋`.

**Scope.**  The bound is unconditional and alphabet-generic, but its constant grows
exponentially in `r`, whereas the Guruswami–Kopparty folded-Wronskian constant
`(k−1)r/(s−r+1)` grows linearly.  So this closes the *existence* of a general-`r` design
statement while leaving the capacity-relevant constant open (`DISCREPANCIES.md`, row O44).

## 40. The folded Wronskian and the `r = 2` subspace-design bound

`RequestProject/Root/CodingTheory/FoldedWronskian.lean` proves the first design bound beyond
`r = 1` that is linear in the degree and independent of the field size.

* `twist γ p` is the polynomial `y ↦ p(γ y)`; `natDegree_twist` and `leadingCoeff_twist`
  give `deg (twist γ p) = deg p` and `lc (twist γ p) = lc(p)·γ^{deg p}` for `γ ≠ 0`.
* `wronsk2 γ p q = p·(twist γ q) − q·(twist γ p)` is the **folded Wronskian**.
* `coeff_wronsk2`: its coefficient in degree `deg p + deg q` is
  `lc(p)·lc(q)·(γ^{deg q} − γ^{deg p})`.
* `wronsk2_ne_zero`: if `γ^m ≠ 1` for all `0 < m < k` (i.e. the order of `γ` is at least
  `k`), then the folded Wronskian of two `F`-linearly independent polynomials of degree
  `< k` is nonzero.  Proof: if the degrees differ, the coefficient above is nonzero; if they
  agree, replacing `q` by `q − c·p` (with `c = lc(q)/lc(p)`) leaves the Wronskian unchanged
  and lowers `deg q`, so a descent on `deg q` finishes.  The hypothesis on the order of `γ`
  cannot be dropped: for `γ` of order `m < k` the independent pair `p = yᵐ`, `q = 1` has
  vanishing folded Wronskian.
* `foldedRS_design_dim_two`: for `s ≥ 2`, `γ ≠ 0` of order at least `k`, and two
  `F`-linearly independent folded codewords `c₁, c₂`, the plane `W = span {c₁, c₂}`
  satisfies `∑_x dim (W ∩ C_x) ≤ 4·(k−1)`.  Proof: a block `x` with `dim (W ∩ C_x) > 0`
  carries a nonzero `a·c₁ + b·c₂` vanishing on the whole block, in particular at the two
  unfolded points `x` and `γx`, so the `2 × 2` system is singular and `x` is a root of the
  folded Wronskian; there are at most `deg ≤ 2(k−1)` such blocks, and each contributes at
  most `dim W ≤ 2`.

Compared with the Guruswami–Kopparty constant `2(k−1)/(s−1)` for `r = 2`, this is larger by
about a factor `2(s−1)`, but unconditional and formal.  It supersedes the exponential bound
of §39 at `r = 2` whenever `q² > 4s`.

## 41. GG25 Stage 1: generic line-decodability implies mutual correlated agreement

`RequestProject/Root/CodingTheory/LineDecodableGeneric.lean` carries out Stage 1 of the GG25
route, for an arbitrary `F`-linear code `C ⊆ (ι → A)` over an arbitrary finite `F`-module
alphabet `A` (so it applies verbatim to folded Reed–Solomon codes, `A = Fin s → F`, and to
ordinary ones, `A = F`).  Radii are absolute (`e : ℕ`), the project-wide convention
`δ = e/n`.

* `IsProximateFamily C e u₀ u₁ Z f` — `f` picks, for every challenge `γ` in the challenge
  set `Z`, a codeword `f γ ∈ C` at distance `≤ e` from the line point `u₀ + γ·u₁`.
* `LineDecodable C e a b` — for every line and every proximate family on a set of at least
  `a` challenges, at least `b` of the proximates are **collinear**, i.e. of the form
  `c₀ + γ·c₁` for one fixed pair of codewords.
* `two_collinear` — `b = 2` is free, so all the content is in large `b`.
* `card_inter_agreement_ge_of_collinear` — the counting core: `b ≥ e + 2` collinear
  proximates force `u₀, u₁` to agree with `c₀, c₁` on a *common* set of `≥ n − e` positions.
* `card_badSet_lt_of_lineDecodable`, `epsMCA_le_of_lineDecodable`,
  `epsMCAmax_le_of_lineDecodable` — hence `ε_mca(C, e) ≤ a/|F|`.

The threshold `e + 2 ≤ b` is sharp: `analysis/line_decodable_implies_mca_check.py` finds,
by exhaustive search over small fields and codes, instances where `LineDecodable C e a (e+1)`
holds and yet `|badSet| ≥ a`; the same script verifies the theorem on 228 lines over 38
random codes.

`RequestProject/Root/CodingTheory/FoldedRSMCA.lean` feeds this with the pair-list bound:
* `epsMCAmax_folded_le_of_four` — if `4e` is below the block minimum distance
  `|B| − ⌊(k−1)/s⌋`, then `ε_mca(foldedRS, e) ≤ (e + 2)/|F|`;
* `folded_threshold_2_128` — with `|B| = 2²⁰` and `|F| ≥ 26·2¹⁵⁸`, `ε_mca ≤ 2⁻¹²⁸`.

The radius reached this way is the unique-decoding-type radius `δ < (1 − ρ_block)/4`, **not**
the capacity radius `1 − ρ − η`; see `DISCREPANCIES.md`, row O49.

## 42. The general-`r` folded Wronskian

`RequestProject/Root/CodingTheory/FoldedWronskianGeneral.lean` lifts §40 from `r = 2` to all
`r`.  With `twist γ p` the polynomial `y ↦ p(γ y)`:

* `foldedWronskianMat γ f` is the `r × r` matrix with entries `twist (γ^t) (f j)`, and
  `foldedWronskian γ f` its determinant;
* `natDegree_foldedWronskian_le` — `deg ≤ r·(k−1)` when every `deg f j < k`;
* `foldedWronskian_ne_zero` — **the main lemma**: if `γ^m ≠ 1` for all `0 < m < k` (order of
  `γ` at least `k`) and `f₀, …, f_{r−1}` are `F`-linearly independent of degree `< k`, then
  the folded Wronskian is nonzero.  The proof is a Casoratian descent: a kernel vector `a`
  of the twisted system is replaced by the cross vector
  `c_j = a_{r−1}·σ(a_j) − σ(a_{r−1})·a_j` (with `σ = twist γ`), one divides out the gcd, and
  the resulting `b` satisfies `σ(b_j) = μ·b_j` for a constant `μ`; comparing top
  coefficients contradicts the order hypothesis.  As at `r = 2`, the hypothesis on the order
  of `γ` cannot be dropped.
* `foldedRS_design_wronskian` — first consequence: for every subspace `W` of the folded code
  with `dim W ≤ r ≤ s`, `Σ_x dim (W ∩ C_x) ≤ r²(k−1)` — polynomial in `r` and independent of
  the field size, superseding the exponential bound of §39.

## 43. GG25 Stage 3: the sharp subspace-design constant `τ(r) = sρ/(s−r+1)`

`RequestProject/Root/CodingTheory/FoldedRSSubspaceDesign.lean` sharpens §42 to the
Guruswami–Kopparty constant, using a **multiplicity** argument.

* `pow_sub_C_dvd_det` — if the columns indexed by `S` of a polynomial matrix all vanish at
  `y`, then `(X − y)^{|S|}` divides the determinant (proved by factoring `M = N · diagonal`
  and `Matrix.det_diagonal`);
* `exists_adapted_basis` — for a subspace `U ≤ Fʳ` there is an invertible `F`-matrix `A`
  with `dim U` of its columns inside `U`;
* `pow_dvd_det_of_kernel` — the corank form: `(X − y)^d ∣ det M` as soon as a
  `d`-dimensional space of vectors is annihilated by `M` evaluated at `y`;
* `sum_rootMultiplicity_le_natDegree`, `sum_rootMultiplicity_comp_le` — distinct points
  contribute disjointly to the degree.

Combining these: if `d = dim (W ∩ C_x)`, then after an `F`-linear change of basis of `W` the
first `d` columns of the folded Wronskian matrix vanish at each of the `s − r + 1` points
`γ^u x` (`0 ≤ u ≤ s − r`), because for those `u` and every row `t < r` one has `t + u < s`,
so the entry evaluates a codeword of `W ∩ C_x` inside the block of `x`.  The folding-domain
hypothesis (GG25 Def. 2.20, already available in the project as `IsFoldingDomain`) makes all
these points pairwise distinct across `x` and `u`, so their multiplicities add up:

* `foldedRS_design_sharp` — **`(s − r + 1) · Σ_x dim (W ∩ C_x) ≤ r·(k − 1)`**;
* `foldedRS_isSubspaceDesign_sharp` — the same statement as the project's generic
  `IsSubspaceDesign` predicate, with `τ(r) = r(k−1)/((s−r+1)·|B|)` for `r ≤ s` (and the
  trivial `τ(r) = 1` beyond).  With `ρ = k/(s·|B|)` this reads `τ(r) ≤ s·ρ·r/(s−r+1)`, i.e.
  the `τ(r) = sρ/(s−r+1)` of the GG25 statement per unit of `dim W`.

This closes row O44 of `DISCREPANCIES.md`.  Hypotheses: `γ ≠ 0` of multiplicative order at
least `k`, `IsFoldingDomain B s γ`, and `r ≤ s`.  Both statements are checked to depend only
on `propext`, `Classical.choice`, `Quot.sound`.  The numerical check
`analysis/folded_wronskian_check.py` found no violation of the sharp bound over its search
space.

## 44. GG25 Theorem 4.7 for lines, and the first capacity-level MCA bound of the project

`RequestProject/Root/CodingTheory/GG25LineDecodable.lean` proves the missing middle stage of
the GG25 route, **with the parameters of the paper**:

```lean
theorem subspaceDesign_implies_lineDecodable {τ : ℕ → ℝ} (hτ : IsSubspaceDesign C τ)
    (r a e : ℕ) (ε : ℝ) (hr : 0 < r) (hτ0 : 0 ≤ τ r) (hεr : 2 / (r : ℝ) ≤ ε)
    (he : (e : ℝ) ≤ (1 - τ r - ε) * Fintype.card ι) :
    LineDecodable C e a ⌈(ε / (r + ε)) * a⌉₊
```

i.e. a `τ`-subspace-design code is `(1, 1 − τ(r) − ε, a, ⌈(ε/(r+ε))·a⌉)`-line-decodable for
every `ε ≥ (ℓ+1)/r = 2/r`.  The condition on `ε` is a **lower** bound and the collinearity
count is `⌈(ε/(r+ε))a⌉`; the earlier working statement (`0 < ε ≤ 1/(2r)`, `b = ⌈εa⌉`) was a
misquotation and is *not* what is proved.

### The argument

The paper's proof (random pruning, GG25 §4.2–4.3) was not available, so a self-contained
argument was reconstructed.  It is a rank count in the **configuration space**
`F × F × (ι → A)`.  For a family of proximates `f` and a set of challenges `T` put

* `psiVec f α = (1, α, f α)`, `curveSpan f T = span {psiVec f α : α ∈ T}`;
* `defectSpace f T = {w : (0, 0, w) ∈ curveSpan f T}` and `defectDim f T` its dimension.

Then `defectDim f T = rank ψ(T) − 2` when `|T| ≥ 2`, `defectSpace f T ≤ C`, and
`defectSpace f T = ⊥` exactly when all proximates over `T` lie on one line of codewords.
Writing `Tᵢ` for the subfamily of challenges whose proximate agrees with the line at
coordinate `i`, and `K = (1 − τ(r) − ε)/ε`, the three pillars are

* `sum_defectDim_le` — **the master inequality** `Σᵢ defectDim f Tᵢ ≤ τ(r)·defectDim f T·n`
  (the subspace-design property applied to `W = defectSpace f T`, using
  `defectSpace f Tᵢ ≤ defectSpace f T ⊓ coordKer i`);
* `defectDim_le_two_mul_K` — **the rank bound** `defectDim f Z ≤ 2K`, obtained from a
  linearly independent subfamily (`|T'| = d + 2`, `|T'ᵢ| ≤ dᵢ + 2`) together with the double
  count `|T|·(n − e) ≤ Σᵢ |Tᵢ|`; this is the only place where `rε ≥ 2` is used, to rule out
  independent subfamilies of size `r + 2`;
* `card_le_one_add_K_mul_defectDim` — **the main induction** (strong induction on `|T|`):
  `|T| ≤ (1 + K·defectDim f T)·b*(T)`, where `b*(T)` is the largest collinear class of `T`.
  The algebra of the step reduces to `(1 − τ(r) − ε)(d − 1) ≥ 0`, and the coordinates at
  which the whole family agrees cancel exactly.

Combining at `T = Z` gives `a ≤ |Z| ≤ (1 + 2K²)·b* ≤ ((r+ε)/ε)·b*`, i.e.
`b* ≥ (ε/(r+ε))·a`, which is the theorem.  The whole statement, and each of the three
pillars separately, were pre-verified by exhaustive exact-rational search over small random
codes in `analysis/gg25_thm47_line_check.py` (no failure).

### Composing the chain

* `epsMCAmax_le_of_subspaceDesign` (same file) plugs the result into the Stage-1 bridge
  `epsMCAmax_le_of_lineDecodable`: for a `τ`-subspace-design code and any
  `a ≥ ((r+ε)/ε)(e+2)`, `ε_mca(C, e) ≤ a/|F|` at every radius `e ≤ (1 − τ(r) − ε)·n`.
  No list-decodability and no minimum-distance hypothesis is needed (row O51 of
  `DISCREPANCIES.md`).
* `foldedRS_isSubspaceDesign_gg25` (`FoldedRSSubspaceDesign.lean`) sharpens the design
  constant to `τ(r) = (k−1)/((s−r+1)·|B|) = sρ/(s−r+1)`, by instantiating
  `foldedRS_design_sharp` at `r := dim W` instead of at the bound `r`.  The previously
  recorded constant carried a spurious extra factor `r`, which alone would make the radius
  `1 − τ(r) − ε` negative in the capacity regime.
* `RequestProject/Root/CodingTheory/GG25FoldedRS.lean` closes the chain for folded
  Reed–Solomon codes:
  * `foldedRS_epsMCAmax_le_gg25` — the general form, with the rate budget
    `k − 1 ≤ ρ·s·n` and the design-slack budget `ρ(r−1) ≤ (η−ε)(s−r+1)`;
  * `foldedRS_epsMCAmax_le_capacity` — the explicit choice `ε = η/2`, `r = 4/η`:
    **at every radius `e ≤ (1 − ρ − η)·n`, `ε_mca(C, e) ≤ (8/η² + 1)·(e+2)/|F|`**;
  * `foldedRS_epsMCAmax_le_two_pow_neg_128` — the concrete instance `n = 2²⁰`,
    `η = 2⁻¹⁰`, `r = 2¹²`, `|F| ≥ 2¹⁷²`, giving `ε_mca ≤ 2⁻¹²⁸`.

This is the project's first **unconditional, capacity-level** MCA bound: the radius is
`1 − ρ − η` rather than a unique-decoding or half-Johnson radius, and no non-degeneracy
hypothesis is carried.

### The constant is not the conjectured one

The requested target was `C = 2n/η + 24/η³` with `|F| ≥ 26·2¹⁵⁸`.  What this route yields is
`≈ 8n/η²` and `|F| ≥ 2¹⁷²`.  The obstruction is structural rather than a slack in the
algebra: the Stage-1 bridge needs `b ≥ e + 2`, hence `a ≥ ((r+ε)/ε)(e+2)`, and for any
admissible pair with `rε ≥ 2` and `ε ≤ η` one has `(r+ε)/ε ≥ 2/ε² ≥ 2/η²`.  So no choice of
`r`, `ε`, `s` inside this argument brings the coefficient of `n` below `≈ 2/η²`.  Row O50 of
`DISCREPANCIES.md` records this.  The composition arithmetic — the design constant, the
budget algebra `τ(r) + ε ≤ ρ + η`, the `b ≥ e + 2` threshold, and the concrete `2⁻¹²⁸`
instance — is checked exactly (integers and `fractions.Fraction`, no floating point) by
`analysis/folded_rs_thm47_check.py`, which reports `PASS`.

All nine new statements are checked by `#print axioms` in `RequestProject/Main.lean` to
depend only on `propext`, `Classical.choice`, `Quot.sound`, and neither new file contains a
`sorry`.

## 45. Strong MCA vs GG25-literal MCA — the two definitions are equivalent

`RequestProject/Root/CodingTheory/GG25LiteralMCA.lean` adds the literal Goyal–Guruswami
definition of mutual correlated agreement (GG25, ECCC TR25-166 / ePrint 2025/2054,
Definition 2.8) in the case `ℓ = 1` and in the perfect version (no proximity loss), and
compares it with the notion the rest of the project bounds.

| notion | definition | current best bound | field size for `2⁻¹²⁸` at `n = 2²⁰`, `η = 2⁻¹⁰` |
|---|---|---|---|
| project's MCA (`StrongMCA`) | `ε_mca(C, e) ≤ err` at every integral radius `e ≤ δ·n`, with the project's `IsBad` | `(8/η² + 1)(e+2)/\|F\|` | `\|F\| ≥ 2¹⁷²` (proved) |
| GG25 MCA (`GG25MutualCorrelatedAgreement`) | GG25 Def. 2.8, `ℓ = 1`, `γ = 0`, relative radii `δ' ≤ δ` | the same bound, via `strongMCA_implies_GG25MCA` | `\|F\| ≥ 2¹⁷²` (proved); the literature suggests `≈ 2¹⁵⁸` is reachable — open |

**What is proved.**

* `strongMCA_implies_GG25MCA` — the project's notion implies the literal GG25 notion.
* `gg25MCA_implies_strongMCA` — and conversely, for positive block length.
* `strongMCA_iff_GG25MCA` — hence the two notions are **equivalent**.
* `gg25BadSet_eq_badSet` — in fact the two bad sets are equal radius by radius, with
  `e = ⌊δ'·n⌋`; the GG25 size condition `|S| ≥ (1 − δ')n` and the project's `n ≤ |S| + e`
  describe the same sets of coordinates (`card_cond_iff`).
* `not_lineAgreeOn_iff` — the mathematical content of the comparison: over a submodule,
  "some point of the line `u₀ + γ·u₁` fails to agree with a codeword on `S`" and "`u₀` or
  `u₁` fails to agree with a codeword on `S`" are the same statement.  One direction is line
  closure; the other follows from the two challenges `γ = 0` and `γ = 1`.
* `foldedRS_gg25MCA_two_pow_neg_128` — the frozen unconditional capacity-level result,
  restated in the literal GG25 language: under the same hypotheses (`n = 2²⁰`, `η = 2⁻¹⁰`,
  `r = 2¹²`, `|F| ≥ 2¹⁷²`), the folded Reed–Solomon code has `(1, 1 − ρ − 2⁻¹⁰, 2⁻¹²⁸)`
  mutual correlated agreement in the sense of GG25 Definition 2.8.

**Honest reading of the constant gap.**  Because the definitions coincide, the difference
between the constant proved here (`≈ 8n/η²`, threshold `2¹⁷²`) and the constant `2n/η +
24/η³` quoted in the literature is **not** a definitional trade-off: both bound the same
quantity.  The gap comes entirely from the proof of GG25 Theorem 4.7 — the random-pruning
argument of GG25 §4.2–4.3 versus the self-contained rank argument reconstructed in
`GG25LineDecodable.lean`, whose bridge to MCA needs `b ≥ e + 2` and therefore pays
`(r+ε)/ε ≥ 2/η²` (see §44 and rows O50, O53 of `DISCREPANCIES.md`).

**Numerical cross-check.**  `analysis/gg25_definition_gap_check.py` computes both bad sets
exactly (integer / `Fraction` arithmetic) for small fields, random linear codes, random
lines and all radii: 1944 instances, 0 mismatches, ratio `strong/GG25` always exactly `1`.

Both notions and all the new statements are `#print axioms`-checked in
`RequestProject/Main.lean` and depend only on `propext`, `Classical.choice`, `Quot.sound`;
the file contains no `sorry`.


## 46. GG25 §4.2–4.3: pinned subspaces, the pruning core, and the sharp (slack) bridge

Three new files implement the mechanism of Goyal–Guruswami §4.2–4.3 and, on top of it, the
sharper route to a capacity-level agreement statement.  Nothing frozen was changed: the
strong notion `epsMCAmax` of `AlphabetMCA.lean`, the bridge `card_badSet_lt_of_lineDecodable`
and the results of `GG25FoldedRS.lean` (in particular the `2¹⁷²` threshold) are untouched.

### 46.1 Pinned subspaces and the deterministic core of `PRUNE` (`PinnedSubspace.lean`)

* `pinnedSubspace H S = H_S = {h ∈ H : h i = 0 for all i ∈ S}` — GG25 Definition 4.4.
* `eq_of_agree_on_of_pinned_eq_bot` — if `H_S = 0`, elements of `H` are determined by their
  restriction to `S` (the reason a successful pruning set decodes uniquely).
* `exists_coord_not_le_coordKer` — one step of `PRUNE`: a nonzero subspace of a
  `τ`-subspace-design code vanishes at fewer than `τ(r)·n` coordinates, so any larger set of
  coordinates contains one at which it does not vanish.
* `exists_pinning_subset` — **the deterministic core**: for `H ≤ C` with `dim H ≤ r`, any
  agreement set `Agr` with `|Agrᶜ| ≤ e ≤ (1 − τ(r) − ε)·n`, and `r < ε·n`, there is
  `S ⊆ Agr` with `|S| ≤ r` and `H_S = 0`.  This is the conclusion that GG25's oblivious
  random algorithm `PRUNE_H` reaches with probability `≥ ε/(r+ε)`; here it is obtained for
  each individual word deterministically, by greedy descent.
* `exists_pinning_of_close`, `ncard_close_le_of_pinning` — the decoding consequences: a
  codeword `c ∈ H` within distance `e` of `y` is singled out inside `H` by at most `r`
  coordinates of `y`, and therefore the number of such codewords is at most the number of
  coordinate sets of size `≤ r` (a list-size bound with no Johnson-type input).

The *probabilistic* form (Lemma C / GG25 Thm 4.5) is **not** claimed; see row O56 of
`DISCREPANCIES.md` for what was checked numerically and why the naive inductive proof for the
weights `Pr[i] ∝ dim H − dim H_i` does not close.  It is not needed here: the line case of
GG25 Thm 4.7, which the pruning argument is used for in the paper, is already proved in
`GG25LineDecodable.lean` with exactly the paper's parameters `ε ≥ 2/r`, `b = ⌈(ε/(r+ε))a⌉`.

### 46.2 The sharp bridge with radius slack (`SharpLineMCA.lean`)

* `card_inter_agreement_ge_of_collinear_slack` — the counting core with slack: `b ≥ 2`
  collinear proximates at radius `e` force `(b − 1)·(n − e − |T|) ≤ e`, hence
  `|T| ≥ n − e − θ` as soon as `e ≤ (b − 1)·θ`.
* `SlackCorrelatedAgreement C e θ err` — for every line: either the whole line agrees with
  the code on one common set of size `≥ n − e − θ`, or a random point of the line is
  `e`-close to the code with probability `< err`.
* `slackCorrelatedAgreement_of_lineDecodable`, `slackCorrelatedAgreement_of_subspaceDesign` —
  the bridge and its composition with GG25 Thm 4.7: `err = a/|F|` for any
  `a ≥ ((r+ε)/ε)·b` with `b ≥ 2 + e/θ`.

### 46.3 Folded Reed–Solomon at capacity, sharp constant (`FoldedRSSharp.lean`)

* `foldedRS_slackCA_gg25`, `foldedRS_slackCA_capacity` — with `ε = η/2`, `r = 4/η` the error
  is `((8/η² + 1)·b)/|F|` for any `b` with `e ≤ (b−1)·θ`, at every radius
  `e ≤ (1 − ρ − η)·n`.  With the natural slack `θ = η·n` this is
  `≈ (8/η³ + 16/η²)/|F|` — **the block length has disappeared from the constant**, in
  contrast with the `8n/η²` of the frozen strong bridge.
* `foldedRS_slackCA_two_pow_neg_128` — the concrete instance: `n = 2²⁰`, `η = 2⁻¹⁰`,
  `r = 2¹²`, slack `θ = 2¹⁰`, `b = 1026`, `a = 2³⁴`; a field of size `2¹⁶²` already gives
  error `2⁻¹²⁸`.

**Comparison, stated carefully.**  The literature figure for folded RS is
`ε_mca ≤ 2n/(η|F|) + 24/(η³|F|)`, i.e. `26·2³⁰` at these parameters, giving the threshold
`26·2¹⁵⁸ ≈ 2¹⁶²·⁷`.  The constant proved here, `8/η³ + 16/η² = 2³³ + 2²⁴`, is of the same
scale (slightly smaller), but the conclusion it supports is *weaker*: correlated agreement
with slack `θ = η·n` in the size of the common agreement set, rather than the strong
(`θ = 0`) statement.  For the strong statement the proved threshold in this project remains
`2¹⁷²` (`foldedRS_epsMCAmax_le_two_pow_neg_128`, unchanged).  Where the loss sits is now
localised precisely: not in the pruning mechanism — whose output is the already-proved
Theorem 4.7 — but in the bridge, which for the strong notion needs `b ≥ e + 2 ≈ n`
collinear proximates (rows O55, O56 of `DISCREPANCIES.md`).

**Numerical pre-verification.**  `analysis/gg25_random_pruning_check.py` (exact rational and
integer arithmetic, no floating point): Part A checks the probabilistic Lemma C for the
residual-dimension weights on 1052 admissible small instances (0 violations, smallest ratio
`55/14`), Part B checks the deterministic pinning statement on 622 instances (0 violations),
Part C checks the slack counting core on 1267 instances (0 violations), Part D prints the
constants and thresholds quoted above.

All new statements are `#print axioms`-checked in `RequestProject/Main.lean` and depend only
on `propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`.

## 47. GG25 Theorem 3.6: amplification of line-decodability, and the literature constant for strong folded-RS MCA

Sections 44–46 left the gap precisely localised (rows O53–O55 of `DISCREPANCIES.md`): the
*pruning* side of GG25 is proved with the paper's parameters, but the **strong** bridge
`line-decodability ⇒ MCA` (`card_badSet_lt_of_lineDecodable`, frozen) consumes
`b ≥ e + 2 ≈ n` collinear proximates, so the small count `b₀ = ⌈(ε/(r+ε))a⌉` coming out of
pruning had to be paid for by multiplying `a` by `n`, giving `≈ 8n/η²` and the threshold
`2¹⁷²`.  GG25 closes that gap with Theorem 3.6: the count is *amplified* from `b₀` to `n+1`
using list-decodability, at the cost of an additive `L·(e+1)` rather than a multiplicative
`n`.  This round formalises that mechanism and the resulting bound.

**Everything here is about the strong (θ = 0) notion `epsMCAmax` of `AlphabetMCA.lean`;
nothing frozen was modified.**  `GG25FoldedRS.lean` (the unconditional `8n/η²` bound with
threshold `2¹⁷²`) and the MCA definitions are unchanged, and `SharpLineMCA.lean` (the slack
formulation of §46) is unchanged.

### 47.1 List-decodability and the pair-collapse lemma (`ListDecodable.lean`)

* `ListDecodable C e L` — for every received word `y`, at most `L` codewords of `C` lie
  within Hamming distance `e` of `y`.
* `ListDecodable.mono`, `listDecodable_of_minDist` — monotonicity, and the unconditional
  instance `L = 1` in the unique-decoding regime `2e < d`.
* `bigPairs u₀ u₁ e` — the set of pairs `(c₀, c₁)` of codewords admitting a *common*
  agreement set of size `≥ n − e` with `(u₀, u₁)`.
* `card_bigPairs_le_of_listDecodable` — **the pair-collapse lemma**: if `C` is
  `L`-list-decodable at radius `e` and `(L+1)² ≤ |F|`, then there are at most `L` big pairs.
  The proof is the challenge-averaging argument: distinct big pairs `(c₀, c₁)` yield distinct
  linear combinations `c₀ + γ c₁` for some single `γ`, because a `γ` collapsing two pairs is a
  root of a nonzero linear polynomial, and there are at most `|Q|(|Q|−1) < |F|` such bad
  challenges; all the collapsed codewords lie within `e` of `u₀ + γ u₁`, so list-decodability
  bounds their number by `L`.

### 47.2 The amplification theorem (`LineDecodableAmplification.lean`)

* `lineDecodable_amplification` — **GG25 Theorem 3.6 for lines.**  If `C` is
  `(1, e, a, t)`-line-decodable with `t ≥ 2` and `e ≤ (t−1)·θ`, and `C` is `L`-list-decodable
  at the slightly larger radius `e + θ` with `(L+1)² ≤ |F|`, then `C` is
  `(1, e, a + L·(b−1), b)`-line-decodable for **every** `b`, in particular for `b = n + 1`.
  The proof is the peeling loop: each application of the weak line-decodability either already
  produces `b` collinear proximates, or produces a class whose associated pair is a *big pair*;
  by §47.1 there are at most `L` big pairs, and each can absorb at most `b − 1` challenges, so
  after removing `L·(b−1)` challenges the weak hypothesis must fire on the good count.
* `epsMCAmax_le_of_lineDecodable_amplified` — the composition with the frozen strong bridge:
  the amplified count `b = e + 2` is admissible, so `ε_mca(C, e) ≤ (a + L·(e+1))/|F|`.

### 47.3 The combined chain (`SharpLineMCAAmplified.lean`)

* `lineDecodable_of_subspaceDesign_count`, `epsMCAmax_le_of_subspaceDesign_listDecodable` —
  subspace design (with the sharp constant `τ(r)`) + pruning count + amplification + strong
  bridge, in one statement: for `a ≥ ((r+ε)/ε)·t` and `e ≤ (1 − τ(r) − ε)·n`,
  `ε_mca(C, e) ≤ (a + L·(e+1))/|F|`.

### 47.4 Folded Reed–Solomon, the literature constant, and the threshold (`FoldedRSMCAFinal.lean`)

* `foldedRS_epsMCAmax_amplified` — the amplified bound for folded RS with general parameters.
* `amplified_budget_le` — the parameter arithmetic: with `ε = η/2`, `r = 4/η`,
  `θ = ⌊ηn/2⌋`, `t = 2 + ⌈e/θ⌉`, `a = ⌈(8/η²+1)t⌉` and `L ≤ 2/η`, the budget satisfies
  `a + L(e+1) ≤ 2n/η + 24/η³`, provided `η ≤ 1/16` and `ηn ≥ 24`.
* `foldedRS_epsMCA_literature` — **the literature constant**: at every radius
  `e ≤ (1 − ρ − η)·n`,

  ```
  ε_mca(C, e)  ≤  2n/(η·|F|)  +  24/(η³·|F|)
  ```

  for the *strong* notion, i.e. the same quantity bounded by the frozen `8n/η²` theorem.
* `foldedRS_threshold_2_158` — **the threshold**: `n = 2²⁰`, `η = 2⁻¹⁰`, `r = 2¹²`,
  `|F| ≥ 26·2¹⁵⁸` give `ε_mca ≤ 2⁻¹²⁸`.  The constant `26 = 2 + 24` is exactly
  `2n/η + 24/η³ = 26·2³⁰` at these parameters.

**What is conditional, stated plainly.**  The two theorems above carry one hypothesis that is
*not* proved in this project: `ListDecodable (foldedRSCode B k s γ) (e + ⌊ηn/2⌋) L` with
`L ≤ 2/η`, i.e. list size `O(1/η)` at gap `η/2` from capacity.  This is the capacity-approaching
list-decoding input of folded Reed–Solomon codes (Guruswami–Rudra and its successors); it is
carried as an explicit hypothesis of the statements, never as an axiom, and it is the *only*
external input.  Every other link — the sharp design constant, the pruning count, the
pair-collapse lemma, the amplification loop and the strong bridge — is proved here.

**Unconditional instances of the amplified bound.**  To show that the hypothesis set is
non-vacuous and that the mechanism is genuinely usable, two corollaries supply the
list-decodability input from results proved in this project:

* `foldedRS_epsMCAmax_amplified_uniqueDecoding` — in the unique-decoding regime
  `2(e + θ) < d` the input is `listDecodable_of_minDist` with `L = 1`, giving the
  unconditional bound `ε_mca(C, e) ≤ (a + e + 1)/|F|`.
* `foldedRS_listDecodable_johnson` (`FoldedRSListDecodable.lean`) — **unconditional
  list-decodability of folded RS in the Johnson regime**, proved by unfolding a folded
  codeword to the evaluation vector of its polynomial on the `s·n` unfolded points and
  applying the Guruswami–Sudan bound already formalised in `ListDecodingGS.lean`: agreement
  on `n − e` blocks is agreement on `T = s(n − e)` unfolded points, and
  `k·(ns)·(m+1) < m·T²` gives `|list| ≤ L` whenever `m·T ≤ k·(L+1)`.
* `foldedRS_epsMCAmax_amplified_johnson` — the amplified strong-MCA bound with **no**
  list-size hypothesis, valid in the Johnson regime.

The remaining open item is therefore sharply delimited: an unconditional `L = O(1/η)`
list-size bound for folded Reed–Solomon *at capacity* (row O57 of `DISCREPANCIES.md`).

**Numerical pre-verification.**  `analysis/gg25_amplification_check.py` (exact integer and
`fractions.Fraction` arithmetic, no floating point) checks, before any Lean was written:
Part A the pair-collapse counting (distinct big pairs give distinct combinations for a good
challenge, and the bad-challenge count is `< |F|` when `(L+1)² ≤ |F|`), Part B the counting
core with slack, Part C the accounting of the peeling loop (`a + L(b−1)` suffices), Part D the
parameter arithmetic `a + L(e+1) ≤ 2n/η + 24/η³` and the `2⁻¹²⁸` threshold at `26·2¹⁵⁸`.
All four parts pass.

All statements are `#print axioms`-checked in `RequestProject/Main.lean` and depend only on
`propext`, `Classical.choice`, `Quot.sound`; there is no `sorry` anywhere in the project.

## 48. Unconditional capacity list decoding of folded Reed–Solomon codes

This section closes row O57: the capacity list-decodability of folded Reed–Solomon codes,
which §47 carried as an explicit hypothesis, is now **proved** — with an honest loss in the
list size, documented below.

### 48.1 The abstract combinatorial core (`CapacityListDecoding.lean`)

Everything is derived from the *sharp* subspace-design inequality already proved in this
project (`foldedRS_design_sharp`), packaged as

```
SharpDesign C s K :  ∀ r ≤ s, ∀ W ≤ C with finrank W ≤ r,
                     (s − r + 1) · ∑ₓ finrank (W ⊓ Ker_x)  ≤  r · K
```

with `K = k − 1` for `C = foldedRSCode B k s γ`.  Two mechanisms turn it into a list bound.

* `card_agree_le_succ_finrank` — **pointwise affine-independence bound.**  For affinely
  independent codewords `p₀, …, p_m` and a received word `y`, at each coordinate `x`
  `#{ t : p t x = y x } ≤ 1 + finrank (V ⊓ Ker_x)`, where `V` is the span of the
  differences: two members agreeing at `x` differ by an element of `Ker_x`, and those
  differences are linearly independent.
* `singleton_bound` — **average-radius relaxed generalized Singleton bound.**  Summing the
  previous bound over the `n` coordinates and inserting the design gives, for any affinely
  independent family of `m + 1` codewords all within distance `e`,

  ```
  (s − m + 1) · (m + 1) · (n − e)  ≤  (s − m + 1) · n  +  m · K .
  ```

  This is exactly the shape `τ(m) = sρ/(s − m + 1)` of the sharp design, and it caps the
  *affine dimension* of any list at capacity by `d₀ = O(1/ε)`.
* `card_le_of_coset` — **coset recursion.**  Inside a coset of a `d`-dimensional subspace
  `V ≤ C`, the codewords agreeing with `y` at a coordinate `x` lie in a coset of
  `V ⊓ Ker_x`; the coordinates where the intersection dimension does *not* drop satisfy
  `(s − d + 1)·|J| ≤ K` by the design.  Double counting gives
  `M · ((s−d+1)(n−e) − K) ≤ (s−d+1)·n·G^{d−1}`, hence `M ≤ G^d`.
* `listDecodable_of_design`, `listDecodable_of_design_top` — combining the two: a list at
  radius `e` spans an affine subspace of dimension `< d₀` by `singleton_bound`, and inside
  such a coset the recursion caps the count by `G^{d₀}`.

### 48.2 The folded Reed–Solomon instance (`FoldedRSCapacityListDecoding.lean`)

* `foldedRS_sharpDesign` — `foldedRS_design_sharp` in the packaged form.
* `foldedRS_capacity_listDecoding` — **the theorem.**  For rate `ρ` (`k − 1 ≤ ρ·s·n`), gap
  `ε ∈ (0,1]`, folding `s` with `8·d₀ ≤ ε·s` and `d₀² + 2·d₀ ≤ s`, `d₀ ≥ 2/ε`, `G ≥ 2/ε`:

  ```
  ListDecodable (foldedRSCode B k s γ) e (G ^ d₀)      for every  e ≤ (1 − ρ − ε)·n .
  ```

* `foldedRS_capacity_listDecoding_ceil` — the canonical instantiation
  `d₀ = G = ⌈2/ε⌉`, under the single clean hypothesis `s ≥ 16/ε² + 8/ε + 3` (so
  `s = Θ(1/ε²)`, exactly the folding parameter of the literature), with list size
  `capacityListSize ε = ⌈2/ε⌉^⌈2/ε⌉`.
* `foldedRS_capacity_listDecoding_exists` — the existential form.

**Honest comparison with the literature.**  The list size proved here is
`(1/ε)^{O(1/ε)}` — the Kopparty–Ron-Zewi–Saraf–Wootters / Tamo level — **not** the
`O(1/ε²)` of Srivastava 2025 nor the optimal `O(1/ε)` of Chen–Zhang 2025.  The reason is
structural and is recorded in row O59 of `DISCREPANCIES.md`: the sharp Singleton counting
above is available only for *affinely independent* tuples, where it is tight; controlling
affinely *dependent* families (which is what the Chen–Zhang induction on folded Wronskians
achieves) was not reconstructed here, and any constant-factor loss in front of `τ ≈ ρ` is
fatal at capacity, so the slack had to be absorbed by the coset recursion at cost `G` per
dimension.

### 48.3 The unconditional MCA bound (`FoldedRSMCAUnconditional.lean`)

* `amplified_budget_le_listSize` — the budget arithmetic of §47 without the assumption
  `L ≤ 2/η`: `a + L(e+1) ≤ L·n + 24/η³`.
* `foldedRS_epsMCA_unconditional` — **the unconditional capacity-level strong MCA bound.**
  With the GG25 parameters `ε = η/2`, `r = 4/η`, `θ = ⌊ηn/2⌋`, `t = 2 + ⌈e/θ⌉`,
  `a = ⌈(8/η²+1)t⌉`, folding `s ≥ 64/η² + 16/η + 3` and `|F| ≥ (L+1)²` with
  `L = capacityListSize (η/2) = ⌈4/η⌉^⌈4/η⌉`, at every radius `e ≤ (1 − ρ − η)·n`:

  ```
  ε_mca(C, e)  ≤  (L·n + 24/η³) / |F| ,
  ```

  with **no list-decodability hypothesis**.
* `foldedRS_epsMCA_unconditional_exists` — the same with the constant packaged
  existentially (and shown positive), as requested.

Nothing frozen was touched: `foldedRS_epsMCA_literature`, `foldedRS_threshold_2_158` and
`GG25FoldedRS.lean` are unchanged; §48 only adds statements.

### 48.4 The concrete threshold, honestly

`analysis/foldedRS_unconditional_threshold.py` (exact integer/`Fraction` arithmetic)
evaluates the three bounds at `n = 2²⁰`, `η = 2⁻¹⁰`, target `ε_mca ≤ 2⁻¹²⁸`:

| bound | list size | required `\|F\|` |
|---|---|---|
| `foldedRS_epsMCA_literature` (**conditional**, needs `L ≤ 2/η`) | `2¹¹` | `26·2¹⁵⁸ ≤ 2¹⁶³` |
| `GG25FoldedRS.lean` `8n/η²` (unconditional, earlier) | — | `2¹⁷¹` |
| `foldedRS_epsMCA_unconditional` (**unconditional**, this section) | `4096⁴⁰⁹⁶ = 2⁴⁹¹⁵²` | `2⁹⁸³⁰⁵` |

For the unconditional bound the *error* constraint alone needs only `|F| ≥ 2⁴⁹³⁰¹`; the
binding constraint is the pair-collapse hypothesis `|F| ≥ (L+1)²`, giving `2⁹⁸³⁰⁵`.  This
is astronomically larger than the `2¹⁵⁸` of the conditional statement and than the `2¹⁷²`
of the earlier unconditional theorem, and it is reported as such: at these parameters the
*conditional* literature chain and the earlier `8n/η²` theorem remain the practically
relevant statements, while §48 is what is currently proved with no external input at
capacity.  Reaching the literature threshold unconditionally requires the `O(1/η)` list
size of Chen–Zhang 2025 (row O59).

### 48.5 Numerical pre-verification

`analysis/foldedRS_capacity_list_check.py` (exact arithmetic over small prime fields, no
floating point) validated every step before any Lean was written, on explicitly generated
folded RS codes: (A) the sharp design inequality, 5982 instances; (B) the pointwise
affine-independence bound, 83709 instances; (C) the relaxed generalized Singleton bound,
28227 instances; (D) the coset recursion inequality, 982 instances; (E) end-to-end list
sizes against `G^{d₀}`, 5600 instances.  Zero violations.

## 49. Srivastava amortisation: a **quadratic** capacity list size `O(1/ε²)`

§48 proved unconditional capacity list decoding of folded Reed–Solomon codes with list size
`⌈2/ε⌉^⌈2/ε⌉`.  The loss sat entirely in the coset recursion `card_le_of_coset`, which pays
a multiplicative factor `G` per dimension.  This section replaces that recursion by an
**amortised two-budget induction** and proves

  `L = 1 + ⌈2/ε⌉² = O(1/ε²)`

under exactly the same hypotheses (`s ≥ 16/ε² + 8/ε + 3`, every radius `e ≤ (1−ρ−ε)·n`).
Everything of §§45–48 is left in place and unchanged.

### 49.1 The mechanism

Let `V ≤ C` with `dim V ≤ d`, `S` a set of codewords in a coset of `V` inside the ball of
radius `e` around `y`, `M = |S|`, `n = |D|`, `m = n − e`, `n_i = dim (V ⊓ Ker_i)`.  Split
the coordinates into `J = {i : n_i ≥ d}` (`a = |J|`) and its complement.

* Double counting: `M·m ≤ ∑_i |S_i|`, `S_i` = the members agreeing with `y` at `i`.
* On `J`: the trivial bound `|S_i| ≤ M`.
* Off `J`: `S_i` lies in a coset of `V ⊓ Ker_i`, of dimension `n_i < d`, so **strong**
  induction gives the *rank-keyed* bound `|S_i| ≤ 1 + n_i·r`.
* Design budget: `a·d + ∑_{i ∉ J} n_i ≤ b d`.

The terms in `a` then cancel **identically** — the coordinates that carry no information are
exactly the ones that consume the budget — leaving the single sufficient condition

  `(★_d)   n + r·b d ≤ (1 + d·r)·(n − e)`,

which for `b d = τ·d·n` follows from `e ≤ (r/(r+1))·(1 − τ)·n` for every `1 ≤ d ≤ r`, with
equality at `d = 1`.  Conclusion: `M ≤ 1 + d·r`, hence `1 + r²` for the whole list (whose
affine dimension is `≤ r` by the average-radius Singleton bound of §48).

### 49.2 Statements

* `Alphabet.card_le_of_coset_amortised` (`SrivastavaInduction.lean`) — the induction above,
  with an abstract budget `b`;
* `Alphabet.listDecodable_of_design_amortised` — assembly with the Singleton dimension
  bound: `ListDecodable C e (1 + dmax·r)` from `SharpDesign C s K`;
* `Alphabet.card_le_of_coset_design`, `Alphabet.list_bound_two_budget`,
  `Alphabet.line_case_bound` (`SrivastavaAbstract.lean`) — the same results in the
  subspace-design language `IsSubspaceDesign C τ` at relative radius
  `δ ≤ (r/(r+1))(1 − τ(r))`, including the line case `|L| ≤ 2` at `δ ≤ (1 − τ(1))/2`;
* `Folded.foldedRS_listDecoding_quadratic`, `Folded.foldedRS_listDecoding_quadratic_ceil`
  (`FoldedRSListDecodingImproved.lean`) — folded RS with `L = capacityListSizeQuad ε
  = 1 + ⌈2/ε⌉²`;
* `Folded.foldedRS_epsMCA_unconditional_quadratic` (`FoldedRSMCAQuadratic.lean`) — the same
  MCA chain as §48 with the improved list size:
  `ε_mca(C, e) ≤ (L·n + 24/η³)/|F|`, `L = 1 + ⌈4/η⌉²`.

### 49.3 The requested bound `(r−1)² + 1` is false

The work order asked for `|L_H(y)| ≤ (r−1)² + 1` at `δ ≤ (r/(r+1))(1 − τ(r))`.  This is
refuted by the repetition code over `F₃` with `n = 3`, which is a subspace design with
`τ ≡ 0`: at `r = 2` the radius is `δ = 2/3`, and for `y = (0,1,2)` the line `C` itself
contains the three codewords `000, 111, 222`, whereas `(r−1)² + 1 = 2`.  The bound proved
here, `1 + d·r`, is tight on this example, agrees with the requested line case at `r = 1`
(`1 + 1 = 2`), and still yields the intended `O(1/ε²)`.

### 49.4 Effect on the field-size threshold

At `n = 2²⁰`, `η = 2⁻¹⁰`, `ε_mca ≤ 2⁻¹²⁸` (exact arithmetic,
`analysis/srivastava_threshold_check.py`):

| list size | `L` | budget `L·n + 24/η³` | `\|F\|` needed |
|---|---|---|---|
| §48, `⌈4/η⌉^⌈4/η⌉` | `2^49152` | `2^49173` | `2^98305` (binding: `(L+1)² ≤ \|F\|`) |
| §49, `1 + ⌈4/η⌉²` | `≤ 2^25` | `≤ 2^45` | `2^173` |

For comparison the earlier unconditional `8n/η²` bound needs `2^171` and the *conditional*
literature constant needs `26·2^158`.  So the capacity-level unconditional statement is now
in the same range as the pre-existing unconditional bound, instead of being astronomically
worse.

The `2^173` row is itself a formal theorem, not just a computation:

| statement | name |
|---|---|
| `n = 2²⁰`, `η = 2⁻¹⁰`, `s ≥ 67125251`, `\|F\| ≥ 2¹⁷³ ⟹ ε_mca ≤ 2⁻¹²⁸`, unconditionally | `Root.CodingTheory.Folded.foldedRS_threshold_quadratic_2_173` |

(file `RequestProject/Root/CodingTheory/FoldedRSMCAQuadratic.lean`; it carries no
list-decodability hypothesis — the list size `L = 1 + 2²⁴` is supplied by
`foldedRS_listDecoding_quadratic_ceil`.)

### 49.5 Numerical pre-verification

Exact integer / `Fraction` arithmetic, no floating point:

* `analysis/srivastava_line_case_check.py` — the line case on brute-forced small linear
  codes over `F₂, F₃, F₅`: 166 963 instances, 0 violations, 1 160 of them tight at 2;
* `analysis/srivastava_induction_check.py` — Part A: the explicit refutation of
  `(r−1)²+1`; Part B: 167 976 coset instances against `1 + d·r`, 0 violations (and 64
  violations of the literal target); Part C: `(★_d)` on 6 600 parameter points and the
  identical cancellation of the `|J|` terms;
* `analysis/srivastava_threshold_check.py` — the table of §49.4.

---

## 50. Linear list size: the excess budget (`ExcessAmortisation.lean`)

This section records the attempt to replace the quadratic list size `L ≤ 1 + ⌈2/η⌉²`
of §49 by a *linear* one.  The outcome is: a complete reduction of the linear bound to a
single, explicitly stated inequality; an unconditional proof of that inequality on affine
layers of dimension `≤ 2`; a formal refutation of the shape of the target statement as it
was posed; and a conditional `2^158` threshold.  **The unconditional threshold of the
repository remains `2^173` (§49).**

### 50.1 The reduction: agreement excess

For a received word `y` and a finite set `S` of codewords put

* `agreeCard y S i = #{c ∈ S : c i = y i}`  (file: `agreeCard`),
* `excess y S = ∑_i (agreeCard y S i − 1)`  (file: `excess`, a real number).

Counting the pairs `(c, i)` with `c i = y i` in two ways
(`sum_agreeCard_eq`) gives, for a set `S` of codewords all inside a ball of radius `e`,

```
|S| · (n − e)  ≤  n + excess y S .
```

Consequently (`card_le_of_excess_le`, `card_le_succ_of_excess_le`):

| hypothesis | conclusion |
|---|---|
| `excess y S ≤ (\|S\| − 1)·T`, `T < n − e` | `\|S\|·(n − e − T) ≤ n − T` |
| additionally `e ≤ (L/(L+1))·(n − T)` | `\|S\| ≤ L + 1` |

So the whole linear-list-size problem is *exactly* the inequality

```
(EXC)      excess y S  ≤  (|S| − 1) · T ,        T = τ(r)·n ,
```

for sets `S` lying in an affine layer of dimension `r`.  Nothing else is needed: `(EXC)`
with `T = τ·n` and radius `(L/(L+1))(1 − τ)n` yields list size `L + 1`, i.e. `L = O(1/ε)`
at capacity, with the optimal constant.

`HasExcessBudget C T` is `(EXC)` as a *hypothesis on the code* (never an axiom), and
`listDecodable_of_hasExcessBudget` turns it into `ListDecodable C e (L+1)`.

### 50.2 Universal pointwise bound

`excess_le_card_sub_one_mul_sum_finrank`: for `S` inside a coset of `V`,

```
excess y S ≤ (|S| − 1) · ∑_i dim (V ⊓ Ker_i) .
```

This is the *unamortised* form; the subspace design bounds the sum by `τ(r)·dim V·n`, which
costs a factor `dim V` — exactly the loss that makes the §49 induction quadratic.  Getting
rid of that factor is the content of `(EXC)`.

### 50.3 Unconditional results

| layer | statement | name |
|---|---|---|
| `dim V ≤ 1` | `excess ≤ (\|S\|−1)·τ(1)·n` | `excess_le_of_finrank_le_one` |
| `dim V ≤ 1` | list `≤ L+1` at `δ ≤ (L/(L+1))(1−τ(1))` | `line_list_bound_linear` |
| `dim V ≤ 2` | `excess ≤ (\|S\|−1)·τ(2)·n` | `excess_le_of_finrank_le_two` |
| `dim V ≤ 2` | list `≤ L+1` at `δ ≤ (L/(L+1))(1−τ(2))` | `plane_list_bound_linear` |

The plane case is the new mathematics.  Its proof is constructive and elementary:

1. two distinct coordinate directions inside a plane intersect in `0`
   (`inf_eq_bot_of_finrank_one`), hence `a_i + a_j ≤ M + 1` for coordinates whose
   agreement classes are *distinct lines* (`agreeCard_add_agreeCard_le`);
2. the design supplies two budgets: `∑_i dim(V ⊓ Ker_i) ≤ 2·τ(2)·n` globally, and, per
   fixed line `L ≤ V`, `#{i : L ≤ Ker_i} ≤ τ(2)·n` — this is the design applied to the
   one-dimensional `L`, with `τ(1) ≤ τ(2)`;
3. a two-variable linear program (`plane_lp`, private) closes the count:
   from `Q ≤ P`, `Q ≤ M − P`, `n₁ ≤ W`, `t ≤ 2W − n₁` follows `n₁·P + t·Q ≤ W·M`.

The result is exactly `(M − 1)·τ(2)·n` with **constant 1** — no slack.  This matters: at
capacity any constant `C > 1` in `excess ≤ C(M−1)τn` destroys the threshold (§50.5).

Compared with §49, which gives `1 + d·r = 1 + 2L` on a plane, this is `L + 1`.

### 50.4 The `+1` is necessary (`LinearListSharpness.lean`)

The mission statement asked for `|list ∩ H| ≤ C₁r + C₂` in the form "list ≤ L at radius
`(L/(L+1))(1 − τ(L))`".  **That form is false**, and the counterexample is formalised:

* `repetitionThree` = the length-3 repetition code over `F₃`;
* `repetitionThree_isSubspaceDesign` — it is a subspace design with `τ ≡ 0`
  (each `C ⊓ Ker_i = 0`);
* at `L = 2`, `n = 3`, the radius `(L/(L+1))(1 − τ(L))·n = 2` and the word `(0,1,2)` is
  within distance `2` of all three codewords `000, 111, 222`:
  `repetitionThree_not_listDecodable_two : ¬ ListDecodable repetitionThree 2 2`;
* `repetitionThree_listDecodable_three : ListDecodable repetitionThree 2 3` — the bound
  `L + 1` is attained, not exceeded.

So `L + 1` (equivalently `C₁ = 1`, `C₂ = 1` in the requested shape) is the sharp constant,
and all statements above are stated in that form.

### 50.5 The threshold that the excess budget buys

`FoldedRSLinearMCA.lean`:

| statement | name |
|---|---|
| `HasExcessBudget (foldedRS …) T`, `T ≤ ρn` ⟹ `ListDecodable … (L+1)` with `L+1 = 2^11` | `foldedRS_listDecodable_linear_of_excessBudget` |
| the same hypothesis ⟹ `ε_mca ≤ 2^-128` at `n = 2^20`, `η = 2^-10`, `\|F\| ≥ 26·2^158` | `foldedRS_threshold_linear_2_158_of_excessBudget` |

The arithmetic is tight: with `θ = 512` and list size `2^11` the requirement is
`e + 512 ≤ (2047/2048)(n − T)`, which holds precisely when `T ≤ ρ·n`.  This is why §50.3
insisting on constant exactly `1` is not pedantry.

### 50.6 Status of `(EXC)` in dimension ≥ 3, and refuted routes

`(EXC)` in general is a sharp fractional subspace-packing inequality:

```
∑_i (occ(K_i) − 1)  ≤  (M − 1) · T ,    T = max_{0 ≠ U ≤ V} (∑_i dim(U ⊓ K_i)) / dim U .
```

Exact-arithmetic search found **no counterexample** (88 brute-forced small linear codes,
300 abstract configurations, 540 excess configurations; scripts in `analysis/`).  Routes
that were tried and *refuted* — recorded so they are not retried:

* multiplicative / Shearer / box-theorem strengthening — the "cross" in `F_q²`;
* the single-flag bound (`FLAGMIN`) — 1 violation in 540 configurations;
* entropy / Han-dual load balancing;
* point-peeling induction;
* `∑_i x_i (M − m(K_i)) ≤ (M−1)T` — fails on the `F_q²` grid;
* submodularity of `U ↦ occ(U) − 1` — fails already in `F³` with two axis lines at
  different heights.

Valid but not sufficient: the coset-splitting recursion
`E(S,V) ≤ ∑_j E(S_j, W) + E(S̄, V/W)` with the exact budget split `B̄ = B_V − B_W`.  It
closes the induction whenever some *proper* subspace attains `T`, and fails only when `V`
itself is the unique maximiser (three lines in a plane is the model case).  This is the
most promising remaining tool for dimension 3.

### 50.7 The geometric root: fractional flag certificates (`FlagCertificate.lean`)

The excess budget can be detached from the coordinates and the design altogether.  A
**fractional flag certificate** for a finite set `S` of words is a finite family of
nonnegative weights `w U` on subspaces `U ≤ C` of rank `≤ r` with

* **budget**   `∑_U w U · dim U ≤ |S| − 1`,
* **covering** `agreeCard y S i − 1 ≤ ∑_U w U · dim (U ⊓ Ker_i)` for every coordinate `i`.

| statement | name |
|---|---|
| a certificate gives the excess budget `excess ≤ (\|S\|−1)·τ(r)·n` | `excess_le_of_flagCertificate` |
| uniform certificates give `HasExcessBudget` … | `hasExcessBudget_of_flagCertificates` |
| … and hence the linear list size `L + 1` | `listDecodable_of_flagCertificates` |
| every affine line carries a certificate | `flagCertificate_of_finrank_le_one` |
| every affine plane carries a certificate | `flagCertificate_of_finrank_le_two` |
| the plane excess budget, re-proved through the certificate, without `τ(1) ≤ τ(2)` | `excess_le_of_finrank_le_two_certificate` |

The proof of `excess_le_of_flagCertificate` is a two-line double count: swap the sums and
apply the design to each `U` separately.  The factor `dim U` that the design produces is
paid for by the *budget*, not by the list size — that is the whole amortisation.

The plane certificate is explicit.  With `L₁` a coordinate line of largest agreement count
`P₁` inside the plane `V`, and `P₂` a bound for the agreement counts of the other
coordinate lines, the weights

```
w L₁ = P₁ − P₂ ,      w V = (|S| − 1 − (P₁ − P₂))/2
```

have weighted dimension exactly `|S| − 1`, and the transversality inequality
`P₁ + P₂ ≤ |S| + 1` is exactly what makes them cover every coordinate
(`flagCertificate_of_plane_occupancies`).  This is strictly stronger than §50.3: the
certificate does not mention `τ` at all, and the derived excess bound no longer needs
`τ(1) ≤ τ(2)`.

**Why the reformulation is the right one.**  For a *fixed* point set `S`, the existence of
a certificate is precisely the linear-programming dual of the excess budget quantified over
**all** coordinate families at once:

```
(D)  max  ∑_K (occ(K) − 1)·y_K       s.t.  ∀ U ≠ 0 : ∑_K dim(U ⊓ K)·y_K ≤ dim U ,  y ≥ 0
(P)  min  ∑_U w_U·dim U              s.t.  ∀ K : ∑_U w_U·dim(U ⊓ K) ≥ occ(K) − 1 ,  w ≥ 0
```

`analysis/fractional_flag_lp.py` solves `(D)` in exact rational arithmetic with a Bland
simplex.  Results:

| ambient | point sets | counterexamples | tight (`value = |S| − 1`) |
|---|---|---|---|
| random over `F₂²`, `F₂³`, `F₂⁴`, `F₃²`, `F₃³`, `F₅²` | 1010 | 0 | frequent |
| **exhaustive** over `F₂³` (all sets containing `0`) | 127 | 0 | 127 |
| **exhaustive** over `F₃²` (all sets containing `0`) | 255 | 0 | 255 |
| **exhaustive** over `F₂⁴`, `\|S\| ≤ 6` | 4943 | 0 | 4943 |

Every single instance is *tight*: the LP value equals `|S| − 1` exactly, as it must, since
the constraint at `K = V` alone forces `∑_U w_U dim U ≥ |S| − 1`.  So the conjecture is
sharp everywhere, which is consistent with the failure of every strengthening listed in
§50.6.

The optimal certificates are integral and supported on very few subspaces — for instance
two skew `4`-point lines in `F₅³` (`|S| = 8`) give `w = 2` on each line and `w = 1` on the
ambient space, total `2 + 2 + 3 = 7 = |S| − 1`.  Two naive greedy rules for producing them
(top-down from the ambient space, bottom-up from the heavy lines) were checked on that
example by `greedy_certificates` in the same script and **both overshoot** — budgets
`25/3` and `22` against the optimum `7` — which is evidence that no purely local rule
constructs the certificate: the LP genuinely balances the weights.  Dimension `≥ 3` therefore remains
open, now in the sharper and coordinate-free form "every finite point set carries a
fractional flag certificate".

## 51. Flat partitions: what the "explicit inductive partition into flats" really gives (`FlatPartition.lean`)

The mission for this round proposed to close the general-dimension flag-certificate gap of
§50.7 by an *explicit inductive partition of the candidate set into flats, whose
**characteristic** weights form the desired flag certificate* ("Chen–Zhang Lemma 2.18").
The instruction also required exact-arithmetic validation before any Lean work.  That
validation refuted the proposed mechanism, so the mission was executed in corrected form:
the partition statement was repaired, proved in full generality, and turned into two
general-dimension certificate constructions; the characteristic-weight step was refuted in
Lean.

### 51.1 The characteristic weights do not cover (refuted)

`analysis/flat_partition_check.py` builds the inductive hyperplane partition of many
candidate sets over small fields and evaluates both constraints of a flag certificate in
exact rational arithmetic.  Result: the *budget* `∑_j dim U_j ≤ |S| − 1` always holds, but
the *covering* constraint fails — 801 covering failures, 0 budget failures.  The canonical
counterexample is a full affine line of `𝔽_q²` (plus, optionally, one point off it): the
peeled partition is `{line, point}` of total dimension `1`, whereas the coordinate on which
the line is constant demands weighted dimension `|S| − 1 = q − 1`.

This is now a theorem, not just a script.  In `𝔽₅²`, with `S` the five points of an affine
line and `y = 0`:

| Lean name | Statement |
|---|---|
| `flagCertificate_unit_weights_fails` | there is a five-point set `S`, contained in a single flat of dimension `1` (so the flat partition `{S}` meets the budget `1 ≤ 4`), such that **no** weighting with all weights `≤ 1` satisfies the covering constraints |

The proof is exact: every subspace of `𝔽₅²` meets `Ker₁` in dimension `≤ 1`, and only
`Ker₁` and the whole plane meet it in dimension `1`, so any family with weights `≤ 1` cuts
out total dimension at most `2`, against the required `|S| − 1 = 4`
(`sum_finrank_inf_coordKer_one_le_two`).  **Certificate weights must scale with the
occupancies; characteristic weights of a flat partition can never do so.**

### 51.2 The corrected partition lemma, in every dimension (proved)

What *is* true, and what the inductive partition argument actually proves, is a statement
about **independent** families of directions rather than about a partition with unit
weights:

> **Independent-flat budget.**  Let `K_j ≤ M` (`j ∈ J`) be independent submodules and let
> `A_j ⊆ S` be subsets of a finite nonempty set `S` with `A_j − A_j ⊆ K_j`.  Then
> `∑_j (|A_j| − 1) ≤ |S| − 1`.

| Lean name | File |
|---|---|
| `IndepOn`, `IndepOn.mono`, `IndepOn.disjoint` | `FlatPartition.lean` |
| `sum_card_sub_one_le_of_indepOn` | `FlatPartition.lean` |

The proof is exactly the inductive partition the mission asked for, in its correct form:
peel the cosets of one direction `K_{j₀}`, observe that every other `A_j` meets each coset
in at most one point (pairwise disjointness of independent directions), recurse in the
quotient `M ⧸ K_{j₀}`, and account `(|S| − p) + (p − 1) = |S| − 1`.  Part B of
`analysis/flag_certificate_general_lp.py` confirms the bound on more than 10⁴ independent
families and confirms that **independence is necessary**: dependent families violate it.

### 51.3 Two general-dimension certificate constructions (proved)

| Lean name | Weights | Hypothesis |
|---|---|---|
| `flagCertificate_of_density` | single weight `(|S| − 1)/dim V` on the layer `V` | no coordinate is denser than the layer: `(a_i − 1)·dim V ≤ (|S| − 1)·dim (V ⊓ Ker_i)` for all `i` |
| `flagCertificate_of_indep_flats` | occupancy excesses `(|T_j| − 1)/dim K_j` on an independent family `K_j` | each coordinate is either trivial (`a_i ≤ 1`) or explained by a flat: `K_j ≤ Ker_i` and `a_i ≤ |T_j|` |

Both hold in **every** dimension, with no restriction on `finrank V` beyond `≤ r`.  The
budget of the second is precisely `sum_card_sub_one_le_of_indepOn`.  Together they cover
the two extreme regimes — uniformly spread sets and sets concentrated on a few independent
flats — and they subsume the dimension-one certificate.  They do **not** cover the mixed
regime (a dense proper subspace inside a larger layer), which is exactly the residual case
of O50.4.

### 51.4 Where the general theorem now stands

`weighted_excess_le_of_flagCertificate` records the exact obstruction structure: a flag
certificate implies

```
∑_i μ_i (a_i − 1) ≤ |S| − 1
```

for **every** nonnegative coordinate weighting `μ` that is *fractionally independent*, i.e.
`∑_i μ_i · dim (U ⊓ Ker_i) ≤ dim U` for every admissible `U`.  This family of inequalities
is precisely the linear-programming dual of the certificate LP, and integral fractionally
independent weightings are exactly independent families of coordinate kernels — for which
§51.2 proves the inequality unconditionally.  So the general existence theorem
(`flagCertificate_of_finrank_le`, target A of the mission) is now reduced to:

> the *fractional* independent-flat budget, plus LP strong duality on the (finite) lattice
> of subspaces.

Mathlib has no linear-programming duality/Farkas theory, so this route cannot be closed
inside the present toolchain without first building it; and the fractional budget itself is
not implied by the integral one.  **Targets A, B and C of the mission therefore remain
open**, and the repository's unconditional threshold remains `2^173` as required by the
freeze list.

### 51.5 The threshold arithmetic under a linear list size

`analysis/chenzhang_linear_threshold_check.py` recomputes, in exact `Fraction` arithmetic,
the field-size requirement `|F| ≥ (L·n + 24/η³)·2^128` at `n = 2²⁰`, `η = 2⁻¹⁰`,
`ε_mca ≤ 2⁻¹²⁸`:

| list size | `|F|` required |
|---|---|
| `L = ⌈2/η⌉ = 2¹¹` (linear) | `26·2^158 = (13/8)·2^162`, i.e. `2^162 ≤ |F| ≤ 2^163` |
| `L = ⌈2/η⌉² = 2²²` (quadratic) | `(515/512)·2^170` |
| `L = ⌈4/η⌉^⌈4/η⌉` (unconditional) | `≈ 2^49300` |

This matches `foldedRS_threshold_linear_2_158_of_excessBudget` exactly.  Note that
`26·2^158 > 2^160`: the mission's success criterion "threshold `≤ 2^160`" is **not** met
even under a linear list size — the correct statement of the target is `26·2^158`
(equivalently `2^163` as a power of two).

## 52. Finite LP duality as the root: Fourier–Motzkin, Farkas, and flag certificates

§51 reduced the general existence of flag certificates to linear-programming duality, which
Mathlib does not provide.  This section builds that duality from scratch and closes the
reduction.

### 52.1 The root theorem: Fourier–Motzkin elimination

`RequestProject/Root/FiniteFarkas.lean` proves, by induction on the number of variables,

```
Root.LP.exists_solution_or_certificate :
  ∀ n (ι : Type u) [Fintype ι] (a : ι → Fin n → ℝ) (β : ι → ℝ),
    (∃ x, ∀ i, ∑ j, a i j * x j ≤ β i) ∨
    (∃ w ≥ 0, (∀ j, ∑ i, w i * a i j = 0) ∧ ∑ i, w i * β i < 0)
```

— a finite system of real linear inequalities either has a solution or a nonnegative
combination of its rows is the zero row with a negative right-hand side.  The proof is
literal Fourier–Motzkin: the rows with a zero last coefficient survive, each
(positive, negative) pair is combined so as to cancel the last coefficient, and the two
directions of the induction step are the *transfer lemma* `fm_transfer` (weights lift
backwards) and the choice of the eliminated coordinate between the largest lower and the
smallest upper bound (solutions lift forwards).  Mathlib's Farkas lemma
(`ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem`) is unusable here: it
needs the closedness of a finitely generated cone, which Mathlib also lacks.

### 52.2 Farkas and LP duality

* `Root.LP.farkas_feasible_iff` — `{x ≥ 0, A x ≤ b}` is feasible iff no `y ≥ 0` with
  `Aᵀ y ≥ 0` has `bᵀ y < 0`; index types arbitrary finite, arbitrary universes.
* `Root.LP.finite_farkas` — the mission's statement,
  `(∀ x ≥ 0, A x ≤ b → cᵀ x ≤ γ) ↔ ∃ y ≥ 0, Aᵀ y ≥ c, bᵀ y ≤ γ`, **for a feasible primal
  system**.
* `Root.LP.finite_farkas_without_feasibility_false` — the feasibility hypothesis cannot be
  dropped.  With `m = n = 1`, `A = 0`, `b = −1`, `c = 1`, `γ = 0` the primal is empty, so the
  bound holds vacuously, while every `y ≥ 0` has `Aᵀ y = 0 < 1 = c`.  This is a Lean
  theorem, not a remark.

`analysis/finite_farkas_check.py` validated all of this in exact `Fraction` arithmetic
before formalisation: over 400 random instances, 0 failures of weak duality, 0 failures of
strong duality on feasible LPs, and 10 instances where the unconditional statement fails —
all of them with an infeasible primal, and the smallest witness is exactly the one above.

### 52.3 Flag certificates *are* the dual variables

`RequestProject/Root/CodingTheory/FlagCertificateFarkas.lean` instantiates the Farkas
feasibility criterion at the certificate LP (variables = the subspaces of a finite candidate
family `Λ`, rows = the budget and one covering constraint per coordinate) and obtains

```
flagCertificateOn_iff_excessBound :
  FlagCertificateOn y S Λ ↔ ExcessBound y S Λ
```

where `ExcessBound y S Λ` is the dual condition: for all `μ ≥ 0` and `lam ≥ 0` with
`∑_i μ_i · dim (U ⊓ Ker_i) ≤ lam · dim U` for every `U ∈ Λ`, one has
`∑_i μ_i (a_i − 1) ≤ lam (|S| − 1)`.  For `lam = 1` this is exactly the fractional
independence obstruction `weighted_excess_le_of_flagCertificate` of §51.4 — so that
necessary condition is now known to be *sufficient* as well.

The mission target follows:

```
flagCertificate_exists_of_excessBound :
  (∀ U ∈ Λ, U ≤ C) → (∀ U ∈ Λ, finrank F U ≤ r) → ExcessBound y S Λ → FlagCertificate y S C r
```

together with the uniform form `hasFlagCertificates_of_excessBound`.

`analysis/flag_certificate_farkas_check.py` checked the equivalence on genuine subspace
instances over `𝔽₂` and `𝔽₃` (real subspaces of `F^{ι×s}`, real coordinate kernels, real
agreement counts): 120 instances, 109 of them feasible, 0 mismatches, exact arithmetic
throughout.

### 52.4 The completed chain

`RequestProject/Root/CodingTheory/FarkasRootChain.lean` threads the root through the
existing machinery:

```
finite Farkas  ⇒  flag certificates  ⇒  excess budget  ⇒  linear list size  ⇒  strong MCA
```

* `hasExcessBudget_of_excessBound` — excess bound + subspace design ⇒ budget `τ(r)·n`;
* `listDecodable_of_excessBound` — ⇒ list size `L + 1`;
* `foldedRS_threshold_linear_2_158_of_excessBound` — ⇒ for folded Reed–Solomon at
  `n = 2²⁰`, `η = 2⁻¹⁰`, list size `2¹¹`: `ε_mca ≤ 2⁻¹²⁸` whenever `|F| ≥ 26·2^158`.

What is still open is no longer a duality question.  The single remaining input is the
excess bound itself — a statement purely about nonnegative coordinate weightings, with the
certificates and the linear programming eliminated.  The repository's *unconditional*
threshold is unchanged at `2^173`, as required by the freeze list, and the honest target
constant remains `26·2^158`, not `2^160`.

### 52.5 The normalised dual criterion

`ExcessBound` quantifies over a scale `lam ≥ 0`; by homogeneity only `lam = 1` and `lam = 0`
matter.  `excessBound_of_unit` reduces the criterion to

* `ExcessBoundUnit y S Λ` — the fractional independence bound at scale `1`, i.e. exactly the
  obstruction family `weighted_excess_le_of_flagCertificate` of §51.4, and
* the degenerate condition that a coordinate seen by *no* candidate subspace carries at most
  one agreement.

`flagCertificate_exists_of_excessBoundUnit` packages this directly as certificate existence.

## 53. The Weighted Excess Bound: the chain is closed

This section records the final link. The excess bound `O52.1`, which §52 had isolated as
the *only* remaining input of the capacity–MCA chain, is now a theorem. Route A of the
mission brief (flat partition → independent directions → occupancy weights) is **not** the
route that works; §53.4 and §53.5 record why, with formal refutations. The route that does
work is a direct induction on the dimension of the layer.

### 53.1 Occupancy (`Root/CodingTheory/Occupancy.lean`)

For a finite `S ⊆ M` and a subspace `W ≤ M`,

```
occ S W = max_{p ∈ S} |{ s ∈ S : s − p ∈ W }|
```

is the largest number of points of `S` in a single coset of `W`. Basic facts:
`occ S ⊥ = 1` for `S` nonempty, `occ S W ≤ |S|`, monotonicity in `W`, and the two counting
lemmas that drive the induction:

* `finrank_map_add_finrank_inf_ker` — rank–nullity for the image of a subspace under a
  linear map;
* `occ_sub_one_le_fibres_add_image` — for a linear `π`, the occupancy excess of `S` splits
  over the fibres of `π` and the image `π(S)`.

### 53.2 The bound (`Root/CodingTheory/WeightedExcessBound.lean`)

```
theorem weightedExcessBound
    (hWV : ∀ i, W i ≤ V) (hS : S.Nonempty) (hSV : ∀ x ∈ S, ∀ y ∈ S, x − y ∈ V)
    (hμ : ∀ i, 0 ≤ μ i) (hlam : 0 ≤ lam) (hfeas : Feasible V W μ lam) :
    ∑ i, μ i * (occ S (W i) − 1) ≤ lam * (|S| − 1)
```

Here `Feasible V W μ lam` is the fractional-independence condition
`∀ U ≤ V, ∑ i μ_i · dim (U ⊓ W i) ≤ lam · dim U`, and `S` lies in a single coset of `V`.

In words: **nonnegative weights that are fractionally independent against every subspace of
the layer cannot accumulate more occupancy excess than the layer itself carries.** This is
exactly the statement that §51.4 had identified as necessary and §52.3 had shown to be
sufficient; it is now proved for all dimensions, with no hypothesis beyond nonnegativity.

The proof is an induction on `dim V`, with an inner induction on the number of indices
carrying nonzero weight, and three steps:

* `web_support_le_one` — if at most one weight is nonzero, the bound is the definition of
  occupancy;
* `web_tight_step` — if some `0 ≠ K ≤ V` is *tight* (the feasibility inequality holds with
  equality at `K`), pick a projection `π` with `ker π = K`, obtained abstractly from
  `Submodule.exists_isCompl`; the fibres of `π` live in the layer `K` and the image lives in
  `V.map π`, both of strictly smaller dimension, so the induction hypothesis applies to each
  and `occ_sub_one_le_fibres_add_image` glues the two halves;
* `exists_exchange` — if nothing is tight, increase one weight until something becomes
  tight. The step length is the minimum of the slack ratios over the (finitely many)
  subspaces of `V`, so the resulting weighting is still feasible and has a tight subspace,
  and one more index has become inactive; the objective only increases.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

### 53.3 The general certificate and the unconditional threshold

`Root/CodingTheory/FlagCertificateGeneral.lean` feeds the bound into the Farkas dual of §52:

* `agreeCard_le_occ` — an agreement count at a coordinate is an occupancy in the layer,
  for the subspace `coordKer i ⊓ V`;
* `excessBound_layerFamily` — hence `ExcessBound y S Λ` holds for the family `Λ` of *all*
  subspaces of the layer;
* `flagCertificate_of_finrank_le` — with `flagCertificate_exists_of_excessBound`, every
  finite candidate set inside a coset of a layer `V ≤ C` with `dim V ≤ r` carries a
  fractional flag certificate of rank `r`;
* `flagCertificate_of_card_le` — in particular every candidate set of at most `r + 1`
  codewords of `C` does, since its differences span at most `|S| − 1` dimensions.

`Root/CodingTheory/ExcessBudgetBounded.lean` records that a budget on *small* candidate sets
is all the list-size argument needs: `HasExcessBudgetUpTo C T m` asks for the excess bound
only on candidate sets of at most `m` codewords, and
`listDecodable_of_hasExcessBudgetUpTo` derives `ListDecodable C e (L+1)` from the budget at
`m = L + 2` (if the list were longer, extract `L + 2` of its elements and contradict the
bound there). `hasExcessBudgetUpTo_of_design` supplies that budget from a subspace design
plus `flagCertificate_of_card_le`, with no extra hypothesis.

`Root/CodingTheory/FoldedRSLinearUnconditional.lean` instantiates the chain:

```
foldedRS_excessBudget                        -- the mission's foldedRS_excessBound
foldedRS_listDecodable_linear_unconditional  -- list size 2^11 for folded RS
foldedRS_threshold_linear_2_158_unconditional
```

The last one is the mission's target, now with **no** excess-budget or excess-bound
hypothesis: for folded Reed–Solomon at `n = 2^20`, `η = 2^-10`, list size `2^11`,

```
26 · 2^158 ≤ |F|   ⟹   ε_mca(1 − ρ − η) ≤ 2^-128.
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`. As required by the freeze list, the
earlier quadratic `2^173` theorem and the conditional `2^158` theorems are untouched.

### 53.4 The proposed independence lemma is false

The brief supplied, as its key new input, the claim that the direction subspaces of a flat
partition are `IndepOn`. **This is false**, and
`Root/CodingTheory/FlatPartitionIndependenceFails.lean` proves it in Lean:

over `𝔽₃`, with `S = {(0,0),(0,1),(0,2),(1,0),(1,1)}` of affine dimension `d = 2`, take

```
H₀ = {(0,0),(0,1)},  H₁ = {(0,2)},  H₂ = {(1,0),(1,1)}
p₀ = (0,0),          p₁ = (0,2),    p₂ = (1,0).
```

The parts are disjoint, cover `S`, and **every** transversal `(h₀,h₁,h₂)` is affinely
independent — `badParts_transversal_affineIndependent`, checked by `decide`. Yet
`K₀ = span{(0,1)} = K₂` and `K₁ = 0`, so `(0,1)` is a nonzero vector of both `K₀` and `K₂`
and the family is not `IndepOn`: `flatPartition_directions_not_indepOn`.

The reason the informal argument fails is structural: the transversal condition constrains
only the relative *positions* of the parts, never their internal *directions*. A part may be
translated along a direction that another part also uses without moving any transversal.
`analysis/flat_partition_independence_check.py` finds 5184 such violations already at
`q = 3, d = 2, |S| ≤ 5`, in exact arithmetic.

### 53.5 Route A cannot work, independently of §53.4

Even granting independence, occupancy weights on a flat partition do not cover. The
hypothesis of `flagCertificate_of_indep_flats` additionally requires every coordinate to be
explained by one part. Take `C = {(a, b, a+b)} ⊆ 𝔽₂³`, `S = C`, `y = (0,0,1)`: all three
agreement counts equal 2, but every flat partition of `S` consists of three singletons, so
every occupancy weight `(|T_j| − 1)/dim K_j` vanishes and coverage fails outright. A
certificate does exist — weight 1 on the rank-2 subspace `C` — so the *conclusion* is fine;
it is the occupancy-weight construction that cannot reach it.
`analysis/correct_flat_partition_check.py` records this instance and sweeps: 19/28, 470/504
and 344/828 instances admit no occupancy-weight certificate.

### 53.6 Two corrections to the mission statements

* `flagCertificate_of_finrank_le` **with no hypothesis at all is false** — already at
  `r = 0`, where a certificate would force `|S| = 1`. The honest statement carries the
  layer: `V ≤ C`, `dim V ≤ r`, and `S` inside a coset of `V`. This is what the mission's
  own downstream use needs.
* `foldedRS_excessBound` for arbitrary candidate sets is likewise unavailable for the same
  reason; the proved form is the bounded one, `HasExcessBudgetUpTo … (r+1)`. It costs
  nothing: the list-size argument only ever inspects candidate sets of `L + 2` codewords.

### 53.7 Numerical validation

All exact `Fraction`/integer arithmetic, no floats.

| script | verdict |
| --- | --- |
| `analysis/flat_partition_independence_check.py` | independence lemma **refuted**, minimal counterexample printed |
| `analysis/correct_flat_partition_check.py` | occupancy-weight construction **fails** on genuine instances |
| `analysis/web_general_lp_check.py` | Weighted Excess Bound verified by exact LP, **0 violations** |

## 54. The unified interpolation-module root for ordinary Reed–Solomon proximity

The mission for this round was to build **one** algebraic root — the generalized
interpolation module of the formal line `w = f₀ + Z·f₁` over `F[Z]`, together with its
Fitting-ideal-style bad locus and its syndrome-space dual — and to use it for a proximity
gap, and then strong MCA, for ordinary Reed–Solomon at the Johnson radius `δ < 1 − √ρ`.

What is delivered is the root itself, both halves of the dichotomy it is meant to produce,
and an unconditional proximity gap valid at *every* radius with a binomial threshold. The
Johnson-scale *linear* threshold is obtained from the root under one explicit, clearly
isolated non-degeneracy hypothesis, which is **not** discharged here; §54.5 states exactly
what is missing.

### 54.1 The root (`Root/CodingTheory/GeneralizedInterpolationModule.lean`)

* `lineInterpModule k L m D g₀ g₁` — the generalized interpolation module

  ```
  M = { Q ∈ F[Z][X][Y] : wdeg_{1,k} Q < L,  mult(Q, (x, g₀ x + Z·g₁ x)) ≥ m  ∀ x ∈ D } ,
  ```

  an honest `F[Z]`-submodule of the trivariate polynomial ring (`mem_lineInterpModule`).
* `lineSyndrome`, `multSyndrome` — the `F[Z]`-linear syndrome map whose components are the
  Hasse coefficients of `Q` at the formal-line points.
* **The duality**, `lineInterpModule_eq_inf_ker`:

  ```
  lineInterpModule k L m D g₀ g₁ = wdegSubmodule k L ⊓ ker (multSyndrome m D g₀ g₁) .
  ```

  The "interpolation module" picture and the "syndrome space" picture are literally the same
  object; this is the unification the brief asked for, and it is a theorem, not a slogan.

### 54.2 The bad locus: pair resultants instead of a discriminant

`pairRes bY bY' x₀ Q Q' = Res_Y(Q(x₀,·,·), Q'(x₀,·,·)) ∈ F[Z]`, and `badLocusIdeal` is the
ideal these generate. Three facts:

| # | Statement | Lean name |
| --- | --- | --- |
| P54a | **Containment.** If the specialised word at `z` agrees with a codeword on a set `A` with the Guruswami–Sudan margin `L ≤ m·|A|`, then `z` is a root of every pair resultant. *No squarefreeness and no non-degeneracy hypothesis.* | `eval_pairRes_eq_zero_of_agreement` |
| P54b | **Degree bound.** `deg_Z pairRes ≤ (bY + bY')·dZ` | `natDegree_pairRes_le` |
| P54c | **Counting / dichotomy.** `|goodZ| ≤ (bY+bY')·dZ` or the pair resultant vanishes identically; hence `ε_mca ≤ (bY+bY')·dZ/|F|` under the pair non-degeneracy hypothesis | `card_goodZ_le_pairRes`, `card_goodZ_le_or_pairRes_eq_zero`, `epsMCA_le_pairRes`, `epsMCAmax_le_pairRes` |

P54a is the concrete gain over the discriminant route of `DiscriminantMCA.lean`: two
specialised interpolants share the linear factor `Y − p_z`, which is all a resultant sees, so
the containment direction needs no hypothesis at all. The hypothesis migrates entirely into
the single statement "some pair of module elements has a nonzero pair resultant".

### 54.3 From a formal witness to correlated agreement

Two theorems close the second half of the route, i.e. the step from an algebraic witness back
to a codeword pair.

* `correlatedAgreement_of_formalWitness` — a bivariate `U(Z,X)` with `deg_X U < k` and
  `deg_Z ≤ d` whose specialisations explain the local witnesses of more than `n·max(d,1)`
  line parameters yields correlated agreement outright, with the explicit pair
  `q₀ = U(0,·)`, `q₁ = U(1,·) − U(0,·)`. The proof is a double count: every position where
  the formal defect `U(Z,x) − f₀x − Z·f₁x` is not identically zero is killed by at most
  `max(d,1)` values of `z`.
* `correlatedAgreement_of_ratFuncWitness` — the sharp form. If the formal line word is
  explained over the *field* `K = F(Z)` by one polynomial of degree `< k` on at least `k`
  positions, the witness is automatically `Z`-affine, `U = c₀ + Z·c₁` with `c₀, c₁ ∈ F[X]` of
  degree `< k`, and `c₀, c₁` agree with `f₀, f₁` on the **whole** agreement set. No counting,
  no lower bound on `|F|`. (Lagrange interpolation over `K` on `k` nodes: the interpolant of
  `Z`-affine data is `Z`-affine.)

### 54.4 An unconditional proximity gap at every radius
(`Root/CodingTheory/OrdinaryRSProximity.lean`)

```
|{ z : Δ(f₀ + z·f₁, RS_{<k}(D)) ≤ e }| > C(n, e)
    ⟹  ∃ q₀ q₁ of degree < k with |{x : f₀ x = q₀ x ∧ f₁ x = q₁ x}| ≥ n − e
```

— `correlatedAgreement_of_card_goodZ_gt_choose`, with **no hypothesis whatsoever** on
`k, e, n, |F|`. In particular the radius is unrestricted: this is a proximity gap at, and
beyond, the Johnson radius. The argument: each good `z` selects an `(n−e)`-subset of the
agreement set of its local witness; two distinct good values selecting the *same* subset `T`
solve a `2 × 2` linear system over `T` whose solution is a codeword pair agreeing with
`(f₀, f₁)` on all of `T` (`exists_line_pair`); otherwise the selection is injective into the
`C(n, n−e) = C(n, e)` subsets.

Corollaries `card_badSet_le_choose_radius`, `epsMCA_le_choose_radius`,
`epsMCAmax_le_choose_radius`: `ε_mca ≤ max(C(n,e), e)/|F|`, at every radius, for the
unchanged strong MCA definition. `CircuitIncidence.lean` already gave the incomparable
all-radius bound `ε_mca ≤ C(n,k+1)/|F|`; the new bound is the sharper one exactly when
`e < k + 1`. What is genuinely new is the proximity-gap *conclusion* (correlated agreement
drawn from the number of good parameters), which a bad-set bound does not give.

### 54.5 What is **not** proved

The target `ordinaryRS_proximity_gap_johnson` with a threshold **linear** in `n` is *not*
established unconditionally. Precisely one step is missing, and it is isolated in the
hypothesis `hnd` of `epsMCAmax_le_pairRes`:

> two elements of the interpolation module of the formal line can be chosen whose pair
> resultant does not vanish identically.

The situation around this hypothesis:

* if it holds, P54a–P54c give the Johnson-scale linear threshold;
* it fails exactly when the two chosen module elements have a common factor of positive
  `Y`-degree over `F(Z)[X]`. Two sub-cases remain open, and neither is claimed here:
  * a common factor *linear* in `Y`, `Y − U`. This is the shape one wants — if in addition
    `U` agrees with the formal line word on `k` or more positions, then
    `correlatedAgreement_of_ratFuncWitness` converts it into exact correlated agreement. That
    additional agreement is *not* automatic from divisibility; deriving it needs a dimension
    count on the cofactor (a cofactor with too little agreement would have to interpolate too
    many points with too few monomials), which is not carried out here.
  * a common factor of `Y`-degree `≥ 2`. A dimension count over the module cannot exclude it
    in the ordinary-RS regime, and excluding it appears to need an effective
    Bertini–Noether-type statement (specialisations of an absolutely irreducible bivariate
    polynomial stay irreducible outside a small set), which is not available in Mathlib.

So the honest summary for ordinary RS is: **root built, both halves proved, dichotomy proved,
unconditional gap with a binomial threshold, Johnson-scale linear threshold conditional on an
explicitly stated non-degeneracy hypothesis.**

Capacity for ordinary RS was not attempted; the brief's freeze list forbids it.

### 54.6 Numerical validation

Exact `Fraction`/integer arithmetic over prime fields, no floats.

| script | verdict |
| --- | --- |
| `analysis/fitting_ideal_bad_locus_check.py` | containment, degree bound, counting and sharpness of the pair resultant: **0 failures** (`p = 13/11`, `n = 5/6`, `k = 2`, `m = 1`); ~1680/3276 resultants nonzero on random lines, 0 nonzero on lines that really are close |
| `analysis/formal_witness_ca_check.py` | double-counting lemma and the `(q₀,q₁)` extraction: **0 failures** |
| `analysis/ordinary_johnson_proximity_check.py` | subset dichotomy, selection map, witness verification: **600 instances, 0 failures** |

## 55. The Fitting-ideal root: verified, and refuted as a route to the Johnson gap

**Mission as received.**  Replace the pair-resultant non-vanishing lemma of
`GeneralizedInterpolationModule.lean` by the 0-th Fitting ideal `Fitt₀(M)` of the generalised
interpolation module `M = lineInterpModule f₀ f₁ k m` over `F[Z]`, prove `Fitt₀(M) ≠ 0`
(target T2), prove that every bad `z` is a root of every element of `Fitt₀(M)` (T3), bound the
degree (T4), and conclude the ordinary-RS Johnson proximity gap (T5–T6).

**What was checked first.**  `analysis/fitting_ideal_root_check.py` (exact integer arithmetic
over small prime fields; no floating point) computes, for many small `(q, n, k, m)`:

* a basis of the interpolation module `M` over `F[Z]` and its torsion;
* the rank of the presentation matrix at each specialisation `Z ↦ z`;
* the set of good `z` (those with `Δ(f₀ + z f₁, C) ≤ δ`).

Two facts came out of every trial:

1. `M` is a **non-zero torsion-free** `F[Z]`-submodule of a free module of larger rank.  For such
   a module the 0-th Fitting ideal of *any* finite generating family is `(0)`.  Target **T2 is
   false as stated**.
2. Good (in particular bad) parameters `z` occur at the **generic** specialised rank — in one run
   all 10 good `z` had the generic kernel dimension.  So the bad locus is *not* contained in the
   rank-drop locus of `M`, and target **T3 is false for every Fitting ideal of `M`**.

Both facts are recorded formally.  `RequestProject/Root/FittingIdeal.lean` develops the missing
theory from scratch (Mathlib has no Fitting ideals of modules — only the unrelated "Fitting
decomposition"):

* `Root.FittingIdeal.fittingIdealZero` — the ideal generated by the determinants of the square
  relation matrices of a generating family;
* `Root.FittingIdeal.det_smul_eq_zero_of_relations`, `fittingIdealZero_le_annihilator` — the
  Cayley–Hamilton/adjugate mechanism: `Fitt₀` annihilates the module;
* `Root.FittingIdeal.fittingIdealZero_eq_bot_of_nonTorsion`,
  `fittingIdealZero_eq_bot_of_torsionFree` — **the refutation**: a non-zero torsion-free module
  has vanishing 0-th Fitting ideal, so no non-vanishing statement of the requested shape can hold
  for the interpolation module itself;
* `Root.FittingIdeal.det_mem_fittingIdealZero_quotient`, `span_quotient_basis`,
  `resultant_mem_fittingIdealZero_bezout` — the *correct* Fitting statement in this setting: the
  resultant of two polynomials is a Fitting element of the **Bézout quotient**
  `R[X]_{<m+n}/range(Sylvester)`, not of the interpolation module.  This is exactly why the
  existing pair-resultant route works and the module route does not.

**Consequence for the mission.**  The pair-resultant lemma of `GeneralizedInterpolationModule.lean`
is *not* a special case of a Fitting-ideal statement about `M`; the Fitting ideal that does the
job is that of a quotient, and for the quotient the resultant already is the generator.  The
Johnson-radius targets T5/T6 therefore remain where §54 left them.

## 56. Agreement-set shortening (`ShorteningMCA.lean`)

The second route asked for is Jo/Chojecki-style **agreement-set shortening**: pin `t` positions
of the agreement set and pass to a shortened generalised Reed–Solomon instance.  This is now
formalised unconditionally.

**Validation first.**  `analysis/shortening_transfer_check.py` (exact arithmetic) verifies on
small instances: the transfer of bad parameters (0 failures in 371 tests), the absence of
double-counting (15 instances), and the Johnson arithmetic.  It also tabulates the least useful
shortening length `t`, which is bounded independently of the dimension (`r = 2, h = 1 → t ≤ 17`;
`r = 4, h = 1 → t = 4`), matching `t ≈ 2h√r/(√r − 1)²`.

**Formal content.**

* `Root.CodingTheory.grsCloseOn_shortWord` — the shortening step: subtracting the Lagrange
  interpolant on `W` turns `IsCloseOn k S f` (with `W ⊆ S`, `|W| ≤ k`) into
  `GrsCloseOn (shortMul W) (k − |W|) (S \ W) (shortWord W f)`.
* `Root.CodingTheory.isCloseOn_of_grsCloseOn_shortWord` — the exact converse, which is what makes
  the *mutual* formulation transfer.
* `Root.CodingTheory.isGrsBad_shorten` — a bad parameter whose witness set contains `W` is a bad
  parameter of the shortened instance, at the **same** error budget.
* `Root.CodingTheory.card_badSet_mul_choose_le` / `card_badSet_le_subJohnson` — the double count
  `#bad · C(|D| − e, t) ≤ C(|D|, t) · B`, where `B` bounds the bad parameters of every shortened
  instance, and `Root.CodingTheory.epsMCA_le_subJohnson` — the same as a bound on `ε_mca`
  (the strong-MCA definition is unchanged).
* `Root.CodingTheory.belowJohnson_of_shortening` — the arithmetic of the reduction, stated over
  `ℕ` with no square roots: from `n·K1 ≤ (S + h)²` (at most `h` units above the Johnson budget)
  and `2Sh + h² + 2St < t(n + K1)` follows `(n − t)(K1 − t) < (S − t)²`.
  `Root.CodingTheory.belowJohnson_2_20_rate_quarter` is the concrete certificate for
  `n = 2²⁰, k = 2¹⁸, h = 1, t = 5`.

**Discharging the sub-Johnson input unconditionally.**  The circuit-incidence machinery of
`CircuitIncidence.lean` is extended from ordinary to *generalised* Reed–Solomon lines:

* `Root.CodingTheory.grsLineCloseOn_of_snd`, `grsCloseOn_snd_of_two`,
  `not_grsCloseOn_snd_of_witness` — the direction-vector criterion for generalised lines;
* `Root.CodingTheory.card_grsBadSet_le_circuit` —
  `#bad · C(T − 1, a − 1) ≤ C(|Dom|, a)` with `T = max(|Dom| − e, k + 1)`, on any sub-domain on
  which the multipliers do not vanish, at **every** error budget;
* `Root.CodingTheory.subJohnsonBound_of_circuit` — hence `SubJohnsonBound` holds unconditionally;
* `Root.CodingTheory.card_badSet_le_shorten_circuit` — the assembled post-Johnson bound with no
  hypothesis beyond the numeric ones.

**Honest scope.**  The assembled bound of `card_badSet_le_shorten_circuit` is unconditional but
*binomial*, not polynomial: the polynomial `O(K⁶)`-type bound needs a **linear** deterministic
bound `B` for generalised lines at the full Johnson radius, which the project has only under the
pair-resultant non-degeneracy hypothesis of §54 (the unconditional linear bound of
`MCAJohnsonGS.lean` reaches only half the Johnson radius, and shortening applied to it caps out
at the unique-decoding radius — see `DISCREPANCIES.md` §8.9).  The polynomial post-Johnson
statement is therefore available in the project only in the conditional form
`epsMCA_le_subJohnson` with `SubJohnsonBound` as an explicit hypothesis, and the numerical prize
certificates were **not** obtained.

## 57. The degeneracy dichotomy: proved, and its degenerate branch refuted

**File:** `RequestProject/Root/CodingTheory/ResultantDichotomy.lean`
**Numerics:** `analysis/dichotomy_resultant_check.py`,
`analysis/degenerate_case_common_factor_check.py`,
`analysis/dichotomy_correlated_agreement_check.py`
(exact integer / `Fraction` arithmetic, no floats).

### 57.1 Mission and outcome in one line

The mission asked to eliminate the `SubJohnsonBound` hypothesis by proving that *either*
some pair of interpolation-module elements has nonzero `Y`-resultant (pair-resultant route),
*or* the degeneracy itself yields a formal witness and hence correlated agreement.

The first half (the dichotomy, target **T1**) is now a theorem.  The second half is
**false**, and the counterexample is formalised.  Consequently target **T2**
(`ordinaryRS_badSet_belowJohnson` without a non-degeneracy hypothesis, and the polynomial
post-Johnson theorem depending on it) is **not** established, and is not claimed anywhere in
the project.

### 57.2 T1 — the dichotomy (proved)

```lean
theorem resultant_dichotomy {T : Set K} (hT : T.Infinite) {V : Set K[X]}
    (hV : ∀ f ∈ V, ∀ g ∈ V, ∀ t ∈ T, f + t • g ∈ V)
    {f₀ : K[X]} (hf₀ : f₀ ∈ V) (hf₀0 : f₀ ≠ 0) :
    (∃ f ∈ V, ∃ g ∈ V, Polynomial.resultant f g ≠ 0) ∨
      (∃ π : K[X], Irreducible π ∧ ∀ f ∈ V, π ∣ f)
```

with the subspace corollary `resultant_dichotomy_submodule` (over an infinite field the
line-closure hypothesis is automatic).  No non-degeneracy is assumed: it is a genuine
dichotomy.  The proof goes through `exists_irreducible_common_factor_of_forall_not_isCoprime`
— if no two elements are coprime then, by an avoidance argument over the infinite parameter
set `T` (`exists_mem_avoiding_irreducibles`), a single irreducible factor of `f₀` must divide
everything.

Two supporting facts complete the resultant dictionary in the setting actually used:

* `resultant_eq_zero_of_common_linear_factor_domain` — a common linear factor kills the
  resultant over any integral domain (Mathlib has the field case; the interpolation module
  lives over `F[Z]`), obtained via `FractionRing` and `Polynomial.resultant_map_map`;
* `pairRes_eq_zero_of_common_witness` — a common factor `Y − U` of two module elements makes
  the specialised pair resultant vanish at **every** point `x₀`.

### 57.3 A correction to the pair-resultant route

```lean
theorem pairRes_eq_zero_of_mem_domain (hx₀ : x₀ ∈ D) … : pairRes bY bY' x₀ Q Q' = 0
```

For `x₀ ∈ D` the two specialised interpolants share the root `f₀ x₀ + Z·f₁ x₀`, so their
resultant is *identically* zero, regardless of degeneracy.  The non-degeneracy hypothesis of
`epsMCAmax_le_pairRes` can therefore only ever be met at a specialisation point `x₀ ∉ D`,
which in particular forces `|F| > |D|`.  The numerics agree exactly: a nonzero specialised
resultant was found at every `x₀ ∉ D` and at no `x₀ ∈ D`.

### 57.4 Refutation of the degenerate branch

```lean
theorem degenerate_branch_without_correlatedAgreement (k L e : ℕ)
    (hkL : k + 1 < L) (hLD : L ≤ D.card) (hke : k + e < D.card) : …
```

The construction: take `u₀ = X^k`, `u₁ = 1` — of `X`-degree *exactly* `k`, one too large to be
a codeword — and the line `f₀ = eval u₀`, `f₁ = eval u₁`.  Then, with
`U = u₀ + Z·u₁ = formalWitnessPoly u₀ u₁`:

* `Q₁ = Y − U` and `Q₂ = X·(Y − U)` both lie in `lineInterpModule k L 1 D f₀ f₁` and are
  `F[Z]`-independent (so the degeneracy is not the trivial rank-one one);
* `Y − U` divides **every** element of the module
  (`dvd_lineInterpModule_of_lineOfWitness`: the Guruswami–Sudan root step still works at
  `X`-degree `≤ k`, not just `< k`), so **every** pair resultant vanishes at every `x₀` and
  the pair-resultant counting route yields nothing;
* yet **no** correlated agreement exists: by `card_agreement_le_of_degree_eq` any codeword of
  degree `< k` agrees with `f₀` on at most `k` positions, so no agreement set of size
  `|D| − e` exists.

So the degenerate branch is non-vacuous and carries no agreement information;
`correlatedAgreement_of_ratFuncWitness` needs a witness of `X`-degree `< k`, and the common
factor produced by the degeneracy has degree exactly `k`.  The separation is sharp — the
numerics record `deg_X(u) < k ⟺ correlated agreement` in every degenerate instance tested.

The converse side is formalised too: `degenerate_branch_with_correlatedAgreement_of_degree_lt`
shows that for a witness line with `deg_X U < k` the module is degenerate in exactly the same
way (common factor `Y − U`, all pair resultants zero) but correlated agreement *does* hold, on
all of `D`, with the codewords `u₀, u₁` themselves.  So the boundary of the degenerate branch
sits precisely at the witness degree, and it is the degree of the common factor's *root*, not
the `Y`-degree of the common factor, that decides.

### 57.5 Numerical validation (exact arithmetic)

* `dichotomy_resultant_check.py` — 70 instances (35 degenerate / 35 non-degenerate): no
  structural violation of the dichotomy; every degenerate instance has a common factor of
  `Y`-degree 1 or 2; nonzero specialised resultants only outside `D`.  Some `m = 2` settings
  report `grid-too-small`: the conservative exactness certificate `deg_X/deg_Z < q` is not met
  at `q = 101`, which is a limitation of the certificate, not a violation.
* `degenerate_case_common_factor_check.py` — 210 instances: 63 degenerate, all with
  correlated agreement; 147 non-degenerate, none with correlated agreement.
* `dichotomy_correlated_agreement_check.py` — exits with status 2 **by design**: of 24
  degenerate instances, 12 (the `just-above-code` family above) have **no** correlated
  agreement.  This is the numerical form of §57.4.

### 57.6 Status of the mission targets

| target | status |
|---|---|
| T1 `resultant_nonzero_or_common_factor` | **proved** (`resultant_dichotomy`) |
| degenerate branch ⇒ formal witness | **refuted** (`degenerate_branch_without_correlatedAgreement`) |
| T2 `ordinaryRS_badSet_belowJohnson` unconditional | **not established** — the route is blocked |
| polynomial post-Johnson, unconditional | **not established** (depends on T2) |

The unconditional binomial post-Johnson bound of §55/56 and all folded-RS results are
untouched.  `SubJohnsonBound` therefore remains a hypothesis of `card_badSet_le_subJohnson`
and its consequences.

Axiom audit for all new results: `propext, Classical.choice, Quot.sound`.

## 58. The Jo-style post-Johnson chain for ordinary RS, and the Chojecki relative radius

Files: `RequestProject/Root/CodingTheory/PostJohnsonJo.lean` (new),
`RequestProject/Root/CodingTheory/ChojeckiRadius.lean` (new), plus two additions to
`ShorteningMCA.lean`.  Axiom audit for every result below: `propext, Classical.choice,
Quot.sound`; no `sorry`, no new axiom.

### 58.1 The single external hypothesis

`SubJohnsonBoundPoly t C` (in `PostJohnsonJo.lean`) is the isolated sub-Johnson input:

> for **every** finite field `F`, domain `D`, deletion set `W` with `|W| = t`, dimension `k`
> and budget `e` with `(|D|−t)(k−1) < ((|D|−t)−e)²` (i.e. the shortened generalised RS
> instance is *strictly below its own Johnson budget*), and every affine line `g₀ + z·g₁`:
> `#bad ≤ C·(k+1)⁶`.

The constant `C` is quantified outside the field, the domain, the dimension and the line —
without that the statement would be vacuous, since a bad set is a subset of `F`.  Nothing else
is assumed: no non-degeneracy, no pair resultants, no Fitting ideals (per the mission's T1).

### 58.2 The chain (T2)

For `n = |D| = r·K`, `r ≥ 2`, `h ≥ 1` and the post-Johnson budget

`E = postJohnsonRadius r K h = ⌊n − √(n(K−1))⌋ + h`,

* `agreementBudget_bounds` — with `S = n − E`: `E ≤ n`, `K − h ≤ S`, `n(K−1) ≤ (S+h)²`
  (at most `h` units above Johnson) and `(S−1)² ≤ n(K−1)` (not more than one below).
* `gain_of_gap` / `subJohnson_of_gap` — if the shortening depth `t` satisfies the *integer*
  gap condition `4(h+t)²r < t²(r+1)²` (the integer form of `2(h+t)√r < t(r+1)`), then for
  `K > 2t(r+1)(2(h+t)+h²+t)` the shortened instance is strictly sub-Johnson:
  `(n−t)((K−1)−t) < (S−t)²`.  This is `belowJohnson_of_shortening` with all thresholds made
  explicit.
* `exists_shortening_depth` — such a `t` always exists: `t = 16·r·h` works for every `r ≥ 2`,
  `h ≥ 1`.
* `choose_le_pow_mul_choose` — the shortening transfer factor is the **constant** `(2r)^t`:
  `C(n,t) ≤ (2r)^t·C(S,t)` whenever `n ≤ 2r(S+1−t)`, which holds here because `S ≥ K − h`.
* `ordinaryRS_badSet_postJohnson_of_subJohnson` — assembling
  `card_badSet_le_subJohnson` (shortening transfer) with the two items above:
  there are `C' = (2r)^t·C` and an explicit `K₀` such that for every field, every domain with
  `|D| = r·K`, `K ≥ K₀`, and every affine line, `#bad(K, E) ≤ C'·K⁶`.
* `ordinaryRS_epsMCA_postJohnson_of_subJohnson` — the same in `ε_mca` form for the unchanged
  strong-MCA definition, maximised over lines: `ε_mca ≤ C'·K⁶/|F|`.

Only `card_badSet_mul_choose_le`, `belowJohnson_of_shortening`, `card_grsBadSet_le_circuit`
and `subJohnsonBound_of_circuit` are used from earlier files, as required.

### 58.3 MDS circuit incidence in Jo's Theorem 4.2 form

`card_grsBadSet_le_circuit_div` and `card_grsBadSet_le_circuit_inf` (in `ShorteningMCA.lean`)
give the quotient and the optimised-over-`a` forms of the unconditional bound

`#bad ≤ min_{k+1 ≤ a ≤ T_eff} C(|Dom|,a) / C(T_eff−1,a−1)`,  `T_eff = max(|Dom|−e, k+1)`,

for generalised RS lines.  No interpolation, no non-degeneracy, no Johnson restriction.

### 58.4 Chojecki: the constant-relative-radius question

The mission's structural lemma `exists_constant_shortening_for_positive_slack` (a **constant**
deletion depth `t` giving positive Johnson slack at a constant post-Johnson relative radius)
is **false**, and the refutation is now formal.

* `not_constant_shortening_for_positive_slack` — for every `ρ ∈ (0,1)`, every `δ ∈ (1−√ρ, 1)`
  and every fixed `t`, there is `N` such that for all `n ≥ N` the shortened instance is still
  (weakly) above its Johnson budget: `(T−t)² ≤ (n−t)(K−t−1)`, `K = ⌊ρn⌋`, `T = n − ⌊δn⌋`.
  Reason: the Johnson deficit is `Θ(n²)` while `t` deletions move each side by `O(t·n)`.
* `exists_linear_shortening_for_positive_slack` — the correct statement needs a **linear**
  depth.  If in addition `ρ < 1 − δ` (the budget is below the MDS distance; without this no
  bound can hold), there is a constant fraction `c` with
  `c* = (ρ−(1−δ)²)/(1+ρ−2(1−δ)) < c < min(ρ, 1−δ)` such that with `t = ⌊c·n⌋` the shortened
  instance is strictly sub-Johnson for all large `n`.
* `two_pow_le_choose_div_choose` — the price: as soon as `2S ≤ n`, the transfer factor of the
  shortening inequality satisfies `2^t ≤ C(n,t)/C(S,t)`.  At `t = ⌊c·n⌋` this is `2^{Θ(n)}`.

**Conclusion.**  Agreement-set shortening can reach a constant post-Johnson relative radius
only at a linear deletion depth, and at linear depth its transfer factor is exponential in
`n`.  A Chojecki-style constant-radius theorem with a polynomial bound therefore cannot be
produced by this route; it needs a different mechanism.  The Jo chain of §58.2 is exactly the
best this route gives: radius `J(ρ) + O(1/n)` with a polynomial `K⁶` bound.

### 58.5 Numerical validation (exact arithmetic, no floats)

* `analysis/post_johnson_internal_check.py` — 90 instances (`r = 2..6`, `h = 1..3`, `K` at and
  far past the threshold): all six implications of §58.2 verified exactly, including the
  transfer bound `C(n,t) ≤ (2r)^t C(S,t)` and the fact that each instance really is
  post-Johnson.
* `analysis/chojecki_relative_radius_check.py` — five `(ρ,δ)` pairs beyond Johnson: every
  fixed `t ∈ {0,1,2,5,10,50,200}` fails for all large `n`; the minimal admissible depth
  `t_min(n)/n` converges to `c*` (within `20/n` in every case); the linear depth
  `⌈c·n⌉` works up to `n = 100000`; and the transfer factor at that depth is measured to be
  `2^{Θ(n)}`.
* The pre-existing `shortening_transfer_check.py` and `circuit_incidence_check.py` still pass.

## 59. The BCHKS25 / Jo sub-Johnson claim: verification, the specialisation-free route, and explicit prize certificates

This section reports on the incoming package that claims a *deterministic* sub-Johnson bound
(BCHKS25 Theorem 4.6 / Jo 2026/1432 Theorem 2.3) with **no non-degeneracy hypothesis**, proved
"by Guruswami–Sudan degree counting and resultant elimination on the formal line", and on the
`2⁻¹²⁸` certificate table that the package derives from it.

### 59.1 Compatibility with the existing formal counterexample — no contradiction, but the route is not enough

`analysis/bchks_subjohnson_vs_dichotomy_check.py` computes, in exact arithmetic and strictly
below the Johnson budget, the true strong-MCA bad set of each instance together with the
status of the resultant route.  The outcome:

* the formal counterexample of §57 (`pairRes_eq_zero_of_mem_domain`,
  `degenerate_branch_without_correlatedAgreement`) is **not** in contradiction with the claimed
  statement: no instance was found whose bad set exceeds the discriminant degree bound where
  that bound applies;
* but the counterexample is not an accident of the *specialisation point* either.  In the
  regime the claimed proof needs — interpolation multiplicity `m ≥ 2`, which is what makes the
  double-root lemma work — **every** instance with a non-empty bad set had a *identically
  vanishing* discriminant: not merely `discLine bY x₀ Q = 0` for `x₀ ∈ D`, but
  `Res_Y(Q, ∂_Y Q) = 0` as a bivariate polynomial, for every element of the interpolation
  module.  The repeated `Y`-factor is `Y − u` with `deg_X u < k`, i.e. the *codeword* of the
  correlated agreement of the instance.

So the resultant/discriminant elimination degenerates exactly on the instances that carry bad
parameters.  The claim "no non-degeneracy hypothesis" cannot be realised by resultant
elimination alone.

### 59.2 A formal barrier: specialised roots do not come from formal roots

`Root.CodingTheory.exists_sqrt_specialisation_of_odd_card` and
`Root.CodingTheory.no_formal_sqrt` (`SubJohnsonBCHKS.lean`) turn that observation into a
theorem: at least half of the parameters `z ∈ F` make `Y² − z` acquire a root in `F`, while
`Y² − Z` has no root over `F[Z]`.  Hence the implication

> the specialised polynomial has a linear factor  ⟹  the formal polynomial has a linear
> factor, outside a bounded exceptional set of parameters

is false in general, and any proof of the sub-Johnson bound must use the coding-theoretic
content (the agreement budget), not only divisibility and degree counting on the formal line.

### 59.3 What *can* be removed: the specialisation point

The non-degeneracy hypothesis of §35 has two parts: the interpolant must be squarefree in `Y`,
and a *good specialisation point* `x₀` must be exhibited.  The second part is removable.

| statement | Lean name |
| --- | --- |
| the discriminant before specialising `X`, `Res_Y(Q, ∂_Y Q) ∈ F[Z][X]` | `discBiv` |
| `discLine bY x₀ Q = (discBiv bY Q).eval (C x₀)` | `discLine_eq_eval_discBiv` |
| the new hypothesis is weaker | `discBiv_ne_zero_of_discLine_ne_zero` |
| `deg_X` bound for the bivariate discriminant | `natDegree_discBiv_le` |
| `discBiv ≠ 0` and `(2bY−1)·dX < \|F\|` produce a good `x₀` | `exists_discLine_ne_zero_of_discBiv_ne_zero` |
| bad-set bound with **no specialisation point** in the hypothesis | `card_badSet_le_discBiv` |
| the `ε_mca` forms | `epsMCA_le_discBiv`, `epsMCAmax_le_discBiv` |

and the reason this matters is itself now a theorem:

| statement | Lean name |
| --- | --- |
| at multiplicity `m ≥ 2` the specialised discriminant vanishes at **every** `x₀ ∈ D` | `discLine_eq_zero_of_mem_domain` |

This is the discriminant analogue of `pairRes_eq_zero_of_mem_domain`; numerically it is
confirmed in `analysis/bchks_subjohnson_degree_check.py`, which also verifies the `deg_X` and
`deg_Z` bounds of the bivariate discriminant and the existence of a good `x₀ ∉ D` whenever the
bivariate discriminant is nonzero.

### 59.4 Generalised Reed–Solomon: the monomial isometry

`Root.CodingTheory.grsBadSet_isometry` and `card_grsBadSet_isometry`: for a nowhere-vanishing
multiplier `v`, the bad set of the generalised line `(g₀, g₁)` equals the bad set of the
rescaled ordinary line `(g₀/v, g₁/v)`.  This is Jo §2, and it is unconditional; any
sub-Johnson bound for ordinary Reed–Solomon lines therefore transfers verbatim to the
shortened generalised lines used by the chain.

### 59.5 Explicit prize certificates at `K = 2¹⁸` (`PrizeCertificates.lean`)

The Jo chain is run at **fixed** `K = 2¹⁸` with the *exact minimal* shortening depth, computed
by integer arithmetic, rather than the `K`-uniform depth `16rh` of `exists_shortening_depth`
(which is far too lossy for certificates).  `postJohnsonRadius_eq_of_sq_bounds` evaluates the
radius `⌊n − √(n(K−1))⌋ + h` exactly, so the certificates are stated at the literal radius.

| rate | `n` | step `h` | radius `E` | depth `t` | transfer `(2r)^t` | admissible `C` | Lean name |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1/4 | 2²⁰ | 1 | 524290 | 4 | 2¹² | `C ≤ 128` | `prize_certificate_rate_quarter_first` |
| 1/8 | 2²¹ | 1 | 1355699 | 2 | 2⁸ | `C ≤ 2048` | `prize_certificate_rate_eighth_first` |
| 1/8 | 2²¹ | 2 | 1355700 | 4 | 2¹⁶ | `C ≤ 8` | `prize_certificate_rate_eighth_second` |
| 1/16 | 2²² | 1 | 3145731 | 1 | 2⁵ | `C ≤ 16384` | `prize_certificate_rate_sixteenth_first` |
| 1/16 | 2²² | 2 | 3145732 | 2 | 2¹⁰ | `C ≤ 512` | `prize_certificate_rate_sixteenth_second` |

Each certificate reads: if `\|F\| ≥ 2²⁵⁵`, `\|D\| = n`, and the sub-Johnson hypothesis
`SubJohnsonBoundPoly t C` holds with the stated `C`, then
`ε_mca(RS_{<2¹⁸}, E) ≤ 2⁻¹²⁸` for the *strong* (mutual) correlated-agreement definition.
They are conditional exactly on the one external ingredient of the chain, and on nothing else.

**The rate `1/2` row of the package's table is not reachable on this route.**
`rate_half_min_depth` shows that at rate `1/2` and `K = 2¹⁸` no depth `t ≤ 14` makes the
shortened instance sub-Johnson, and `rate_half_budget_exceeded` shows that the transfer factor
`4¹⁵` of the minimal depth `t = 15` already pushes the bound past `2¹²⁷`, so **no** value of
the sub-Johnson constant yields `2⁻¹²⁸` over a field with fewer than `2²⁶⁵` elements.  The
same computation rules out rate `1/4` at the second integer step.
`analysis/prize_certificate_check.py` records the whole table in exact integer arithmetic.

### 59.6 Status of the mission targets

| target | status |
| --- | --- |
| `badSet_le_subJohnson_bchks` proved without non-degeneracy | **not proved**; §59.1–59.2 show the proposed route cannot give it |
| specialisation point removed from the non-degeneracy hypothesis | **done** (`card_badSet_le_discBiv`) |
| generalised-RS transfer | **done, unconditional** (`grsBadSet_isometry`) |
| `SubJohnsonBoundPoly` removed from `PostJohnsonJo.lean` | **not done** (it is still the single external hypothesis) |
| explicit `2⁻¹²⁸` certificates | **done for four of the five requested rows, conditional on `SubJohnsonBoundPoly`**; the rate-`1/2` row is refuted for this chain |

## 60. The sub-Johnson hypothesis was mis-shaped: refutation, correction, and what the prize table really costs

### 60.1 One line

The single external input of the Jo-style post-Johnson chain, as isolated in §58 —
`SubJohnsonBoundPoly t C`, "the bad set of a shortened generalised line below its own Johnson
budget has at most `C·(k+1)⁶` elements" — is **false**, for every deletion depth `t` and every
constant `C`.  It is refuted by an explicit counterexample
(`Root.CodingTheory.subJohnsonBoundPoly_false`, `SubJohnsonRefutation.lean`).  The defect is
the *shape* of the bound, not the underlying mathematics: the literature's `J(N, d, E)` is a
polynomial in the **length** `N`, and the corrected hypothesis
`Root.CodingTheory.SubJohnsonBoundLen t C` (bad set `≤ C·(|D|+1)⁶`) survives the
counterexample.  Rerunning the chain with the corrected hypothesis costs a factor `(2r)⁶`,
and that factor is exactly what puts the published `2⁻¹²⁸` table out of reach over the
prescribed field size.

### 60.2 The counterexample

Fix `t` and `C`.  Take a prime `p > t + 64C + 2`, `F = 𝔽_p`, `D = F`, delete any `t`
positions (`W`, `|W| = t`, `v = shortMul W`, `Dom = D \ W`), and take **dimension `k = 1`**
with the generalised line

```
g₀(x) = x²·v(x) ,   g₁(x) = x·v(x) ,   budget  e = |Dom| − 2 .
```

The sub-Johnson condition of the hypothesis reads `(|D| − t)·(k − 1) < ((|D| − t) − e)²`,
i.e. `0 < 4`: it holds.  For any two surviving positions `x ≠ ±y` the parameter
`γ = −(x + y)` is bad, with witness set `S = {x, y}`:

* on `S` the line point equals the **constant** `−xy` times `v`
  (`x² − (x+y)x = −xy = y² − (x+y)y`), so it is a generalised codeword of dimension one;
* `g₀` is not a constant multiple of `v` on `S`, since `x² ≠ y²`; hence the whole line is not.

This is `Root.CodingTheory.isGrsBad_quadratic_pair`.  Fixing `x` and letting `y` range over
`Dom \ {x, −x}` gives at least `p − t − 2` *distinct* bad parameters, because
`y ↦ −(x + y)` is injective.  The claimed bound is `C·(k+1)⁶ = 64·C`, a constant.  Since `p`
is free, the hypothesis fails.

The moral is structural: pairs of surviving positions already produce linearly many bad
parameters, so **no** bad-set bound that ignores the length can hold.

### 60.3 The corrected hypothesis and the chain

`Root.CodingTheory.SubJohnsonBoundLen t C` replaces `C·(k+1)⁶` by `C·(|D|+1)⁶`.  With it:

* `Root.CodingTheory.card_badSet_le_shortening_len` — the chain at fixed parameters, numerator
  `(2r)^t·C·(r·K + 1)⁶`;
* `Root.CodingTheory.epsMCAmax_le_two_pow_neg_128_len` — the numerical form: numerator `≤ 2^b`
  and `|F| ≥ 2^(b+128)` give `ε_mca ≤ 2⁻¹²⁸`;
* `Root.CodingTheory.ordinaryRS_badSet_postJohnson_of_subJohnsonLen` and
  `Root.CodingTheory.ordinaryRS_epsMCA_postJohnson_of_subJohnsonLen` — the asymptotic Jo
  statement `#bad ≤ C'·K⁶`, `ε_mca ≤ C'·K⁶/|F|`, now with `C' = (2r)^t·C·(2r)⁶`.

So the *shape* `O_{r,h}(K⁶)` of the Jo conclusion is unaffected by the correction; only the
constant is, and only by the fixed factor `(2r)⁶`.

### 60.4 The numerical cost, at `K = 2¹⁸` (`analysis/prize_certificate_length_check.py`)

With the exact minimal shortening depths of §59 and the constant `C = 1`:

| rate | `n` | `t` | `log₂` numerator | `≤ 2¹²⁷`? | field that does certify `2⁻¹²⁸` |
|------|-----|-----|------------------|-----------|-------------------------------|
| 1/2  | 2¹⁹ | 15  | 144 | no | 2²⁷³ |
| 1/4  | 2²⁰ | 4   | 132 | no | 2²⁶¹ |
| 1/8  | 2²¹ | 2   | 134 | no | 2²⁶³ |
| 1/8 (h=2) | 2²¹ | 4 | 142 | no | 2²⁷¹ |
| 1/16 | 2²² | 1   | 137 | no | 2²⁶⁶ |
| 1/16 (h=2) | 2²² | 2 | 142 | no | 2²⁷¹ |

Formally: `Root.CodingTheory.prize_budget_exceeded_rate_*` prove `2¹²⁷ < (2r)^t·1·(rK+1)⁶` for
all six rows, and `Root.CodingTheory.prize_len_certificate_rate_*` prove the six positive
certificates over the field sizes in the last column.

Reading: over a field with `q < 2²⁵⁶` a bad-set bound of at most `2¹²⁷` is needed for
`ε_mca ≤ 2⁻¹²⁸`.  With the length-based numerator this forces a sub-Johnson constant strictly
below one — between `2⁻⁵` (rate 1/4, first step) and `2⁻¹⁷` (rate 1/2) — which the stated
`O(N/η⁵)` shape does not supply.  Either the field must grow by `5`–`17` bits beyond `2²⁵⁶`,
or the sub-Johnson bound must come with an explicitly sub-unit leading constant.

### 60.5 Status of the earlier conditional certificates

`PrizeCertificates.lean` is unchanged and still builds; its five certificates are true
implications with a false antecedent, hence vacuous.  Both that file and `PostJohnsonJo.lean`
now carry a header note pointing at the refutation and at the corrected file.  Nothing in the
folded-RS capacity results, the binomial fallback, or the strong MCA definition was touched.

## 61. The affine factor split: a length-based bad-set bound for the formal line

`RequestProject/Root/CodingTheory/AffineFactorSplit.lean`.

### 61.1 The obstruction that the split removes

`Root.CodingTheory.card_badSet_le_disc` bounds the bad set of a formal line by the degree of
the discriminant `Res_Y(Q, ∂_Y Q)` of the line interpolant, on the hypothesis that this
discriminant is nonzero.  That hypothesis is *never* satisfiable in the regime of interest:

> `Root.CodingTheory.discLine_eq_zero_of_correlatedAgreement` — if `f₀`, `f₁` agree with
> codewords `A`, `B` of degree `< k` on a set `S` obeying the two double-root margins
> (`L ≤ m·|S|`, `L' ≤ (m−1)·|S|`, `L ≤ L' + k`), then `(Y − (A + z·B))²` divides the
> specialised interpolant at *every* parameter `z`, so `discLine bY x₀ Q = 0` outright
> (as soon as `(2·bY − 1)·dZ < |F|`).

Correlated agreement is exactly the configuration a proximity-gap statement must handle, so
the discriminant route degenerates precisely where it is needed.  This is a formal barrier of
the same kind as `pairRes_eq_zero_of_mem_domain`, and it is now proved rather than conjectured.

### 61.2 The split

Write the interpolant as

    Q  =  (∏_{(A,B) ∈ Pairs} (Y − (A + Z·B)))  ·  R

— the affine linear factors coming from genuine codeword pairs, times a residual `R` — and
demand non-degeneracy only of `R`.  Two lemmas close the count.

* **Per-pair counting** (`Root.CodingTheory.card_badPairSet_le`): a *fixed* pair `(A,B)`
  explains at most `|D|` bad parameters.  Proof: if `z` is bad with witness `A + z·B` on a
  witness set `S`, then `S` must contain a *spurious* position `x`, i.e. one with
  `f₁(x) ≠ B(x)` and `(f₀ − A)(x) + z·(f₁ − B)(x) = 0` (`exists_spurious_position`); such a
  position determines `z` uniquely, so distinct bad parameters consume distinct positions.
* **Residual double root** (`Root.CodingTheory.sq_dvd_residual`): a bad parameter whose
  witness is not the specialisation of any split-off affine factor forces a double root of
  `R`, hence is a root of the discriminant of `R`.

Together (`Root.CodingTheory.card_badSet_le_affineSplit`):

    |bad|  ≤  (#Pairs)·|D|  +  (2·bY(R) − 1)·dZ(R)

with `#Pairs ≤ bY(Q)` (`card_badSet_le_affineSplit_ydeg`), and the MCA form
`Root.CodingTheory.epsMCA_le_affineSplit`.  This is a **length-based** bound of the BCHKS25
shape `|bad| = O(|D|)` — not the refuted dimension-based shape.

### 61.3 An unconditional corner

`Root.CodingTheory.card_badSet_le_affineSplit_linear`: if the residual is *linear* in `Y`, no
non-degeneracy hypothesis is needed at all (a `Y`-degree `≤ 1` factor cannot acquire a double
root), and `|bad| ≤ (#Pairs)·|D| + dZ(R)` holds outright.

### 61.4 Numerical support (exact arithmetic, no floats)

* `analysis/affine_split_badset_check.py` — 24 brute-force instances over `GF(5)`, `GF(7)`,
  `GF(11)` confirm that every witness is affine in `z` and that the per-pair count never
  exceeds `|D|`.
* `analysis/slack_interpolant_dimension_check.py` — verifies the slack (variables > equations)
  condition exactly.  At a fixed margin `T ≥ (9/8)·√(k·n)`, rate `1/2`, `m = 10`, the two
  constants are *independent of the length*: `bY = 15` and `dZ = 109` for every
  `n = 2¹²…2²²`, giving `|bad| ≤ 15n + 2117 ≈ 15n`.  At near-Johnson radii for `n = 2²⁰`
  (rate `1/2`, `m = 50`): `δ = 49/171` against the Johnson radius `169/577`, `|bad| ≤ 2.1·10⁸`,
  which certifies `ε_mca ≤ 2⁻¹²⁸` over a field of about `2¹⁵⁶` elements — far smaller than the
  `2²⁶¹`–`2²⁷³` of the §60 chain.

### 61.5 Scope

The split **weakens** the non-degeneracy hypothesis (from the whole interpolant to the
residual factor) and changes the bound's shape to the correct length-based one; it does not
eliminate the hypothesis.  See `DISCREPANCIES.md` §8.14.  Everything above is `sorry`-free and
uses only `propext`, `Classical.choice`, `Quot.sound` (`RequestProject/Main.lean`).

### 61.6 The split always exists, and the hypothesis is intrinsic

Two later additions remove the two least natural features of §61.2.

* `Root.CodingTheory.exists_affine_split` — **every** nonzero `Q` factors as a product of
  affine linear factors `Y − (A + Z·B)` times a residual carrying *no* affine linear factor
  (induction on the `Y`-degree in the UFD `F[Z][X][Y]`).  So the factorisation hypothesis
  `hfac` is not a restriction at all: it can always be met, and by `card_pairs_le_ydeg` the
  number of split-off factors is at most `bY`.
* `Root.CodingTheory.card_badSet_le_affineSplit_discBiv` — the residual hypothesis is stated
  with the *bivariate* discriminant (`R` squarefree in `Y` over `F(Z)(X)`), which mentions no
  specialisation point `x₀` and is strictly weaker than `discLine bYR x₀ R ≠ 0`
  (`discBiv_ne_zero_of_discLine_ne_zero`), at the cost of the harmless field-size condition
  `(2·bY(R) − 1)·dX < |F|`.

Combining them, `Root.CodingTheory.badSet_le_or_residual_degenerate` is a hypothesis-free
*dichotomy* for an arbitrary line interpolant: the canonical affine split exists, has at most
`bY` factors and an affine-factor-free residual `R`, and *whenever* `R` meets the schedule's
degree bounds and is squarefree in `Y`, the length-based bound

    |bad| ≤ bY·|D| + (2·bY(R) − 1)·dZ(R)

holds.  The code-level form is `Root.CodingTheory.epsMCAmax_le_affineSplit_discBiv`: a uniform
split over all lines with at most `P` affine factors gives
`ε_mca ≤ (P·|D| + (2·bY(R) − 1)·dZ(R)) / |F|`.

The one remaining assumption is therefore exactly one statement: *the affine-factor-free
residual of the canonical split is squarefree in `Y`*.  Equivalently, the interpolant has no
repeated non-affine factor.  Nothing weaker suffices: repeated affine factors are handled
(they enter `Pairs` with multiplicity), and repeated non-affine factors would require a
Hilbert-irreducibility-type transfer that is not available (see `DISCREPANCIES.md` §8.14).

## 62 The squarefree kernel of the residual: the factorwise bound, and why the kernel alone
   cannot remove the hypothesis

`RequestProject/Root/CodingTheory/SquarefreeKernelResidual.lean` (sorry-free, standard axioms
only).  §61 left exactly one open hypothesis: *the affine-factor-free residual `R` of the
canonical split is squarefree in `Y`* (`discLine bYR x₀ R ≠ 0`).  Two ways of removing it were
proposed:

1. "a residual free of affine linear factors is automatically squarefree in `Y`";
2. "replace `R` by its squarefree kernel `R_sf = R / gcd_Y(R, ∂_Y R)`; every parameter `z` at
   which the specialised residual acquires a multiple `Y`-root is then a root of
   `Disc_Y(R_sf)`, of `Z`-degree at most `(2·b_Y(R_sf) − 2)·d_Z(R)`".

### 62.1 Both proposals are false — formally

* `Root.CodingTheory.sqExample` is the residual `R = (Y − Z²)²` in `F[Z][X][Y]`.
* `Root.CodingTheory.sqExample_no_affine_factor` — it has **no** affine linear factor
  `Y − (A + Z·B)`, `A, B ∈ F[X]`; it is a legitimate residual of the canonical split.
* `Root.CodingTheory.exists_affineFactorFree_not_squarefree` — its discriminant vanishes
  identically at every specialisation point, so **proposal 1 is refuted**.
* `Root.CodingTheory.discLine_sqExampleKernel_eq_one` — its squarefree kernel `Y − Z²` has
  discriminant the constant `1`: no roots at all.
* `Root.CodingTheory.sq_dvd_specZ_sqExample` — yet at **every** parameter `z` the specialised
  residual has the double root `Y = z²`.
* `Root.CodingTheory.sqfreeKernel_bound_fails` — packaging the four: the proposed bound
  `(2·b_Y(R_sf) − 2)·d_Z(R)` equals `0` while the double-root locus is all of `F`.  **Proposal 2
  is refuted**, at every parameter and by a margin of `|F|`.
* `Root.CodingTheory.doubleRootLocus_card_unbounded` — the quantified barrier: over `ZMod p`
  the same residual has kernel `Y`-degree `1` and double-root locus of size `p`.  Hence *no*
  function of the degrees of the squarefree kernel can bound the double-root locus.

The mechanism behind the refutation: a repeated factor `S^e` (`e ≥ 2`) turns every root of a
specialisation of `S` into a *double* root of the specialisation of `R`, and those roots are
invisible to `Disc_Y(R_sf)`.  Exact-arithmetic confirmation for `(Y − Z²)²` and `(Y² − Z)²`
over `F₅, F₇, F₁₁, F₁₃`: `analysis/sqfree_kernel_check.py`.

### 62.2 The correct positive statement: a factorwise bound

* `Root.CodingTheory.sq_dvd_mul_trichotomy` — over a field, `(Y − p)² ∣ S₁·S₂` implies that
  `(Y − p)²` divides one of the factors, or that `Y − p` divides both.
* `Root.CodingTheory.resLine` / `natDegree_resLine_le` / `eval_resLine` — the formal
  `Y`-resultant of two pieces of the residual, an element of `F[Z]` of degree `≤ (b₁+b₂)·d`.
* `Root.CodingTheory.eval_locus_eq_zero_of_sq_dvd_mul` — a double root of the specialisation of
  `R₁·R₂` makes `z` a root of `Disc_Y(R₁)`, of `Disc_Y(R₂)`, or of `Res_Y(R₁,R₂)`.
* `Root.CodingTheory.card_badSet_le_affineSplit_twoFactor` and
  `Root.CodingTheory.epsMCA_le_affineSplit_twoFactor` — the resulting bad-set and `ε_mca`
  bounds for a residual written as `R = R₁·R₂` (e.g. squarefree kernel times cofactor):

      |bad| ≤ (#Pairs)·|D| + (2b₁−1)·d + (2b₂−1)·d + (b₁+b₂)·d ,

  under the three hypotheses `Disc_Y(R₁) ≠ 0`, `Disc_Y(R₂) ≠ 0`, `Res_Y(R₁,R₂) ≠ 0`.

The third hypothesis is exactly what a repeated factor destroys (`Res_Y(S,S) = 0`), which is
the precise price of multiplicities.  So the conditionality of §61 is *localised*, not removed:
the length-based sub-Johnson bound remains conditional on the residual having no repeated
non-affine factor.  The unconditional results of the project are unchanged: the pair-cover
bound `epsMCAmax_le_pairCover_gs` (radius `1 − (ρ(1+1/m))^{1/4}`) and the unique-decoding /
independent-folds chain.

### 62.3 Auxiliary lemmas of independent use

* `Root.CodingTheory.discRes_eq_zero_of_sq_dvd_domain` — the formal-degree discriminant
  vanishes at a square linear factor over any **domain** (the earlier version needed a field);
  proved by transport along the inclusion into the fraction field.
* `Root.CodingTheory.discLine_eq_zero_of_sq_dvd_biv` — a square factor `Y − w` of the residual,
  with `w ∈ F[Z][X]` arbitrary (not necessarily affine in `Z`), kills `discLine` identically at
  every evaluation point.

### 62.4 The exact obstruction

* `Root.CodingTheory.resultant_eq_zero_of_common_factor` — a common non-unit factor makes the
  formal-degree resultant vanish (over a field, at any formal degrees above the true ones).
* `Root.CodingTheory.discRes_eq_zero_of_sq_factor` — over **any domain**, a repeated factor of
  positive degree kills the formal-degree discriminant.
* `Root.CodingTheory.discLine_eq_zero_of_sq_factor` and
  `Root.CodingTheory.no_sq_factor_of_discLine_ne_zero` — hence `discLine bYR x₀ R ≠ 0` holds
  **iff** the residual has no repeated factor surviving the specialisation at `x₀`: the
  hypothesis of `card_badSet_le_affineSplit` is exactly "no repeated factor", affine or not.

### 62.5 Empirical status of the remaining hypothesis

`analysis/residual_squarefree_check.py` builds, with exact arithmetic in `F_q(Z)(X)`, the
Guruswami–Sudan interpolation module of concrete formal lines (random ones and ones planted
with correlated agreement) and measures `deg_Y gcd(Q, ∂_Y Q)` for the least-`Y`-degree
interpolant.  On all 24 instances tried (`q ∈ {101,127}`, `n ≤ 7`, `k ∈ {2,3}`, `m = 2`) that
gcd is trivial: the interpolant — hence its residual — is squarefree in `Y`, so the remaining
hypothesis holds there; in most instances the interpolant is even linear in `Y`, which is the
unconditional corner `card_badSet_le_affineSplit_linear`.  The exactness of the grid method
caps the degrees by `q`, so this does not probe the large-multiplicity regime; it is evidence
for, not a proof of, the hypothesis.

## 63. Phase 0: is the separable-kernel hypothesis necessary?  Exact-arithmetic answer, and the Welch–Berlekamp pencil that replaces it in the unique-decoding regime

The brief for this pass forbade writing any Lean before the separable-kernel hypothesis had
been probed numerically, with exact arithmetic only, along three axes: (1) can a degenerate
residual occur on a genuine Guruswami–Sudan interpolant, (2) does the *whole* interpolation
module degenerate or only the canonical minimal-degree representative, (3) can the bad set be
read off the syndrome module alone, with no interpolant and no discriminant.  All three
experiments were run to completion in exact arithmetic over `F_q` and `F_q(Z)(X)`; no floating
point is used anywhere.  The scripts are

* `analysis/explore_degenerate_residual.py` → `analysis/phase0_experiment1_output.txt`
* `analysis/space_of_interpolants.py`       → `analysis/phase0_experiment2_output.txt`
* `analysis/direct_bad_locus_from_syndrome.py` → `analysis/phase0_experiment3_output.txt`

### 63.1 Experiment 1 — degeneracy does occur on real interpolants, but it never bites

96 instances passed the Guruswami–Sudan validity filter `m·t ≥ L`, and the GS root property
was verified in every one of them (0 failures), so these are genuine interpolants and not
artefacts of a broken construction.  The split into content and affine-linear factors was
performed and the residual `R` inspected.

| outcome | count |
|---|---|
| residual squarefree in `Y`, correlated agreement present | 51 |
| residual squarefree in `Y`, no correlated agreement | 18 |
| residual **not** squarefree in `Y`, no correlated agreement | 27 |
| residual not squarefree in `Y`, correlated agreement present | 0 |
| instances without correlated agreement violating the licensed bound | **0** |

The first conclusion is negative for the naive reading of the hypothesis: **a genuine GS
interpolant can have a non-squarefree residual while the line has no correlated agreement at
all.**  Twenty-seven such instances are recorded verbatim in the output file (e.g.
`q=101, n=6, k=2, t=5, m=2, L=9` with `deg_Y R = 2`, `deg_Y gcd(R, ∂_Y R) = 1`).  So the
hypothesis is not automatic and cannot be discharged by an argument that only inspects the
interpolant's degrees.

The second conclusion is the important one.  In every one of those 27 degenerate instances the
bad set was tiny — between 0 and 3 parameters — far inside the bound the theorem wants to
license (12, 18, 30, 40 in the respective configurations).  Not a single instance without
correlated agreement violated the licensed bound.  So:

> **The separable-kernel hypothesis is sufficient but not necessary (category 2 of the
> brief).**  Its failure does not produce a large bad set; it only destroys the particular
> discriminant-based *certificate* of smallness.

### 63.2 Experiment 2 — the degeneracy is a property of the *choice* of `Q`, not of the module

For each instance the full `F_q(Z)`-linear space of interpolants obeying the BCHKS25 degree
bounds was computed by exact Gaussian elimination over `K = F_q(Z)`, and 19–25 members of the
module were sampled with `F_q[Z]` coefficients, contents divided out, and
`deg_Y gcd(Q, ∂_Y Q)` computed over `L = F_q(Z)(X)`.  The archived run covers seven of the
eight configurations; the eighth (`q=101, n=7, k=2, m=3`) was stopped for time and the
conclusions below are drawn from the seven that completed.

* In the instances where the canonical minimal-`Y`-degree interpolant is degenerate, **18–23
  of the 19–25 sampled interpolants from the same module are squarefree**.  Degeneracy is an
  artefact of the minimal-degree choice, not an intrinsic obstruction.
* The module gcd is `0` (no common factor) on every non-CA instance.  On the
  correlated-agreement instances the module gcd is exactly the planted affine factor, of
  degree 1 — which is the honest, structural obstruction and the one the theory expects.
* The price of insisting on a squarefree representative is a slightly larger bad-locus degree:
  the minimal-degree choice gives 12, 18, 30 in three representative configurations, while the
  best squarefree choice in the sampled space gives 15, 24, 40.

So a better choice of `Q` removes the degeneracy without any kernel machinery — at the cost of
a constant-factor-worse degree bound.  This is a genuine alternative route, but it does not by
itself remove the hypothesis: to *prove* that a squarefree representative always exists one
needs exactly the statement that the module is not contained in the non-squarefree locus, and
that is again a Hilbert-irreducibility-flavoured claim.

### 63.3 Experiment 3 — syndrome-only detection works, but only below the unique-decoding threshold

Writing the syndrome of the line as a pencil `A + z·B` over `F_q`, the *rank-drop set*
`drop_e` was computed exactly and compared with the true bad set `bad_e`.

* `bad_e ⊆ drop_e` in **all 150** instances (0 containment failures).  The rank test never
  misses a bad parameter.
* In the informative regime `2e < n − k` (66 instances) with a non-degenerate pencil (37
  instances) the rank test gives `|drop_e| ≤ e + 1` in every case, and in 34 of 37 it is
  *exactly* the bad set.  So syndrome-only detection is not merely sound, it is essentially
  tight.
* For `2e ≥ n − k` the rank test is vacuous: `drop_e` is all of `F_q` in 84/84 instances.  The
  method has no content past the unique-decoding threshold, which is the honest limitation.
* **11 exact counterexamples to "degenerate pencil ⟹ correlated agreement"** were found, all in
  the constructed *rational* family.  A degenerate pencil is therefore strictly weaker than
  correlated agreement.

### 63.4 Answers to the four questions of the brief

1. **Is the kernel hypothesis necessary?**  No.  It is sufficient but not necessary: it fails
   on 27 of 96 genuine GS instances, and on none of them does the conclusion fail.
2. **Does a better low-`Z` interpolant exist?**  Yes, essentially always: the overwhelming
   majority of the module is squarefree even when the canonical representative is not.  The
   penalty is a constant factor in the bad-locus degree.
3. **Does syndrome-only detection work?**  Yes, and it is sharp — but only strictly below the
   unique-decoding threshold `2e < n − k`.  Past it the test degenerates completely.
4. **Recommended formalisation route.**  Because the syndrome route is exactly sharp where it
   applies and needs neither interpolation, nor factorisation, nor discriminants, it is by far
   the cheapest thing to formalise unconditionally.  That is the route taken in §63.5.  The
   separable-kernel route remains the only candidate *past* Johnson, and it must be stated as
   an explicit hypothesis, never as a lemma.

### 63.5 The Welch–Berlekamp pencil, formalised

`RequestProject/Root/CodingTheory/WelchBerlekampPencil.lean` (no axioms, no `sorry`) turns
Experiment 3 into theorems.  For a line `z ↦ f₀ + z·f₁` on `D` and radius `e`, the pencil is
the `|D| × (k + 2e + 1)` matrix over `F[Z]` whose row at `x` expresses
`Λ(x)·(f₀ x + Z·f₁ x) = Q(x)`.

* `exists_wbPair_of_isCloseOn` — the key equation: closeness on a set whose complement has at
  most `e` points produces a nonzero Welch–Berlekamp pair `(Λ, Q)` with `deg Λ ≤ e`,
  `deg Q < k + e`, valid at *every* point of `D` (not just on the agreement set).
* `natDegree_wbDet_le` — every maximal minor is a polynomial in `Z` of degree at most `e + 1`.
  Only the `e + 1` locator columns carry `Z`, and each carries it linearly; the proof is the
  Leibniz expansion together with `Fintype.prod_sum_type`.
* `wbDet_eval_eq_zero_of_isBad` — every bad parameter is a root of every maximal minor.
* `card_badSet_le_of_wbDet_ne_zero` and `epsMCA_le_of_wbDet_ne_zero` — **one** nonvanishing
  maximal minor already gives `|bad| ≤ e + 1` and `ε_mca ≤ (e+1)/|F|`.  This is the theorem
  that Experiment 3 predicted, with the same constant `e + 1`.
* `wbDet_eq_zero_of_rationalLine` and `wbDet_eq_zero_of_correlatedAgreement` — degeneracy is
  implied by correlated agreement, and more generally by the line being *rational* of
  denominator degree `≤ e`.  So the non-degeneracy hypothesis is not vacuous and its failure
  has a precise structural meaning.
* `not_isCloseOn_of_not_dvd` — the formal counterpart of the 11 counterexamples: for a
  rational line `Λ·f₀ = P₀` with `k + 2e ≤ |D|`, `e`-closeness of `f₀` forces `Λ ∣ P₀`.  Hence
  if `Λ ∤ P₀` the word `f₀` is not `e`-close to the code at all, while the pencil is
  identically degenerate.  Degeneracy is strictly weaker than correlated agreement, proved,
  not merely observed.
* `exists_nonzero_wbVector_of_card_lt` — sharpness: if `|D| < k + 2e + 1` the system has a
  nonzero solution for *every* word, so the test carries no information.  This is the exact
  formal analogue of the 84/84 vacuous instances of Experiment 3.

The file also contains the classical single-parameter Welch–Berlekamp decoder, which is what
makes the pencil argument legitimate: `wbPair_cross` (in the unique-decoding regime
`k + 2e ≤ |D|` any two Welch–Berlekamp pairs of the same word satisfy `Λ·Q' = Λ'·Q`),
`wbPair_eq_mul_of_isCloseOn` (hence a pair of a word that is `e`-close has numerator exactly
`Λ·p`, so the pair *reads off* the codeword) and `isCloseOn_of_wbPair_mul` (the converse: a
pair whose numerator factors as `Λ·p` with `deg p < k` certifies agreement with `p` outside the
`≤ e` roots of `Λ`).

Compared with the project's previous unconditional line bounds — `card_badSet_le_succ`
(requires `k + 3e ≤ |D|`) and `card_badSet_le` (requires `3e < |D| − k + 1`) — the pencil
gives the same constant `e + 1` under the weaker hypothesis `k + 2e < |D|`, at the price of the
explicit non-degeneracy assumption, which is now a checkable rank condition on a concrete
matrix rather than a statement about factorisations.

What is **not** proved, and is the honest remaining gap on this route: in the degenerate
branch the bad set was small in every instance tried, but the only thing that follows formally
from a global kernel vector `(Λ, Q)` over `F[Z]` is a bound of the order of `deg_Z Λ + deg_Z Q`,
i.e. of the order of `k + 2e`, which is no better than the pair-cover bound the project already
has.  Closing that branch would need control of the pseudo-remainder of `Q` by `Λ` in `Y`, and
is left open; it is *not* assumed anywhere.

### 63.6 Subresultant probe (partial)

`analysis/subresultant_bad_locus_check.py` (→ `analysis/subresultant_validation1_output.txt`)
replaces the discriminant of the separable kernel by the first nonvanishing principal
subresultant of `(R, ∂_Y R)`.  Of 56 instances, 9 were usable — the rest were rejected because
the `Z`-specialisation drops the degree ("interpolation invalid") or because the residual has
`Y`-degree `< 2` — and on all 9 usable instances, all of which have a genuinely non-squarefree
residual (`j > 0`, typically `j = 1`), there were **0 containment failures** and **0
degree-bound failures**: every bad `z` is a root of `sres_j`, and `deg_Z sres_j` stays below
`(2 b_Y − 2)·d_Z` with room to spare (4 against 12 in the typical case).  Nine usable instances
is too thin a base to draw a conclusion from, and this is recorded as a probe, not a result.

## 64. Frozen: the seven unconditional Welch–Berlekamp pencil theorems

This section is the **freeze record** of the Welch–Berlekamp (WB) pencil strand.  All seven
statements below live in `RequestProject/Root/CodingTheory/WelchBerlekampPencil.lean`, are
`sorry`-free, introduce no `axiom`, and are audited in `RequestProject/Main.lean` by
`#print axioms`: each depends on exactly `propext`, `Classical.choice`, `Quot.sound`.

"Unconditional" here means what it means everywhere else in this file: the theorem carries no
hypothesis that the project has failed to prove elsewhere and no side conjecture.  The
hypotheses that do appear (`1 ≤ k`, `k + 2e ≤ |D|`, `wbDet … ≠ 0`, …) are explicit,
statement-level, and checkable on the concrete data.

| # | Theorem (`Root.CodingTheory.…`) | One-line meaning |
| --- | --- | --- |
| W1 | `natDegree_wbDet_le` | every maximal minor of the pencil is a polynomial of degree `≤ e + 1` in the line parameter `Z` |
| W2 | `card_badSet_le_of_wbDet_ne_zero` | one non-vanishing maximal minor already forces `#bad ≤ e + 1` on the line |
| W3 | `epsMCA_le_of_wbDet_ne_zero` | the same bound in probability form: `ε_mca ≤ (e+1)/\|F\|` |
| W4 | `wbDet_eq_zero_of_correlatedAgreement` | correlated agreement at radius `e` makes *every* maximal minor vanish identically |
| W5 | `wbDet_eq_zero_of_rationalLine` | so does a *rational* line `f_i = P_i/Λ` with `deg Λ ≤ e` — degeneracy is strictly more common than correlated agreement |
| W6 | `not_isCloseOn_of_not_dvd` | for such a rational line with `k + 2e ≤ \|D\|` and `Λ ∤ P₀`, the word `f₀` is not even `e`-close to the code: the converse of W4 is false |
| W7 | `exists_nonzero_wbVector_of_card_lt` | sharpness: if `\|D\| < k + 2e + 1` the WB system has a nonzero solution for *every* word, so the whole test is vacuous above unique decoding |

Reading the table as one statement: **W1–W3 are the positive theorem** (a rank certificate on
a concrete `(k+2e+1) × (k+2e+1)` matrix over `F[Z]` gives the sharp bad-set bound `e + 1`),
**W4–W6 delimit its hypothesis** (its failure is implied by correlated agreement, but is *not*
equivalent to it — W5/W6 are a proved counterexample family, not a numerical observation), and
**W7 is the sharpness of the regime** (`k + 2e < |D|`; nothing on this route survives past it).

### 64.1 What the pencil changes for ordinary RS

The project's previous unconditional line bounds for ordinary Reed–Solomon in this regime were
`Root.CodingTheory.card_badSet_le_succ` (hypothesis `k + 3e ≤ |D|`, from `SyndromeRigidity.lean`)
and the trivial `card_badSet_le` (`#bad ≤ |D|`).  W2/W3 give the *same* constant `e + 1` under
`k + 2e < |D|`, i.e. the whole unique-decoding regime, at the price of a rank condition that is
checkable rather than conjectural.  The trade is recorded as D64.1 in `DISCREPANCIES.md`.

### 64.2 What it does not change

Nothing beyond unique decoding.  W7 proves this route cannot be pushed past `k + 2e < |D|`.
The post-Johnson picture — the unconditional binomial fallback
`card_badSet_le_shorten_circuit`, the conditional length-based bound `card_badSet_le_affineSplit`
/ `epsMCA_le_affineSplit` and its residual hypothesis, the pair-cover bound
`epsMCAmax_le_pairCover_gs`, and all folded-RS results — is untouched by this section.  See
`MILESTONE_ORDINARY_RS.md` for the assembled frontier.

## 65. The separable-component list: the list-indexed reassembly of the residual bound

`SquarefreeKernelResidual.lean` had the *two-factor* reassembly.  This section records its
generalisation to a finite **list** of components, in the new file
`RequestProject/Root/CodingTheory/SeparableComponentList.lean` (sorry-free; every declaration
audited by `#print axioms` in `RequestProject/Main.lean` to depend only on `propext`,
`Classical.choice`, `Quot.sound`).

### 65.1 The component list (T1) and its two criteria (T2)

`Root.CodingTheory.SeparableComponents F ι` bundles a finite index set `idx`, components
`poly i` of `F[Z][X][Y]`, formal `Y`-degrees `bY i`, a common `Z`-degree bound `dZ` and an
evaluation point `x₀`, together with the two nondegeneracy conditions

* `disc_ne_zero`  — `Disc_Y(R_i) ≠ 0` for every component (separability in `Y`);
* `res_ne_zero`   — `Res_Y(R_i, R_j) ≠ 0` for `i ≠ j` (pairwise coprimality in `Y`).

The residual is the **plain product** `SeparableComponents.prod = ∏ i ∈ idx, poly i`: the list
is multiplicity-free (§65.5 explains why it must be).

The two criteria are supplied by
`discLine_ne_zero_of_separable` (exact degrees + `Separable` ⇒ nonzero discriminant) and
`resLine_ne_zero_of_isCoprime` (exact degrees + `IsCoprime` ⇒ nonzero resultant), and packaged
as the constructor `SeparableComponents.ofSeparableCoprime`, which takes field-level algebraic
data instead of resultant nonvanishing.

`discLine_X_sub_C_eq_one` and `resLine_X_sub_C` compute the two certificates for monic linear
components (`Disc = 1`; `Res = u(x₀) − v(x₀)`), and `twoComponentWitness` /
`twoComponentWitness_prod` exhibit an explicit inhabitant over any field — the residual
`(Y − Z)·(Y − Z²)` — so the structure is not vacuous.

### 65.2 Containment (T3)

`sq_dvd_finset_prod_cases`: over a field, if `(Y − p)²` divides a finite product then it
divides one factor, or `Y − p` divides two distinct factors.

`eval_locus_eq_zero_of_sq_dvd_prod`: consequently, if the square of `Y − p` divides the
specialisation at `z` of `∏ i ∈ s, R i`, then

    (∃ i ∈ s, Disc_Y(R_i)(z) = 0)  ∨  (∃ i ≠ j ∈ s, Res_Y(R_i,R_j)(z) = 0).

### 65.3 The summed bad-set bound (T4)

`card_badSet_le_affineSplit_components` (and its `ε_mca` form
`epsMCA_le_affineSplit_components`, and the bundled `card_badSet_le_components`):

    |bad| ≤ (#pairs)·|D| + ∑_{i ∈ s} (2b_i − 1)·d + ∑_{(i,j) ∈ s.offDiag} (b_i + b_j)·d ,

for an interpolant that splits as affine linear factors times `∏ i ∈ s, R i`.  The last sum is
over *ordered* pairs, hence twice the informal `∑_{i<j}`.  For `#s = 1` this is
`card_badSet_le_affineSplit`; for `#s = 2` it is `card_badSet_le_affineSplit_twoFactor` with the
resultant term doubled.

### 65.4 Post-Johnson under an explicit hypothesis (T5)

`SeparableComponentSplit r h a` is the explicit structural/field-size hypothesis: over every
field with `a·K² ≤ |F|` and every line on a domain of size `r·K`, the interpolant admits the
affine split with a multiplicity-free, separable, pairwise-coprime component list whose
schedule budgets are `#pairs, #components, b_i ≤ a·K` and `d ≤ a·K²`.  Under it:

* `card_badSet_postJohnson_separable_explicit` — `|bad| ≤ (a·r + 2a³ + 2a⁴)·K⁶` at the
  post-Johnson radius `E = ⌊n − √(n(K−1))⌋ + h`, `n = r·K`;
* `ordinaryRS_badSet_postJohnson_separable` — the `∃ C` form requested by the brief;
* `ordinaryRS_epsMCAmax_postJohnson_separable` — the `ε_mca` form, `≤ C·K⁶/|F|`;
* `separable_prize_certificate` — a `2⁻¹²⁸` certificate: `2¹²⁸·C·K⁶ ≤ |F|` suffices.  At the
  prize parameters `r = 2`, `K = 2¹⁸` this is `|F| ≥ 2²³⁶·C`, against the `2²⁶¹ … 2²⁷³` of the
  shortening chain of §60: the component route removes the `(2r)^t·binomial` overhead, at the
  price of the component-split hypothesis.

### 65.5 What the route does *not* do — recorded honestly

* **Multiplicities are not admissible.**  The brief's `R = ∏ R_i^{e_i}` version of the bound is
  false; the counterexample `(Y − Z²)²` is already proved in this project
  (`sqfreeKernel_bound_fails`, `doubleRootLocus_card_unbounded`).  The exact-arithmetic search
  `analysis/separable_component_counterexample_search.py` confirms that each of the three
  hypotheses — separability, pairwise coprimality, multiplicity-freeness — is load-bearing, with
  explicit counterexamples over `F₅ … F₂₃`.
* **The conditionality is localised, not removed.**  Classically
  `Disc(fg) = Disc(f)·Disc(g)·Res(f,g)²`, so the componentwise hypotheses *imply* that the whole
  residual is squarefree in `Y`; `analysis/separable_component_check.py` verifies this in all
  750 admissible random instances (column `C5`).  The gain is that the hypothesis is now
  componentwise and checkable, and that the bound is stated for a residual presented in factored
  form; the gain is *not* a weaker assumption.  This is recorded as D65.3 in `DISCREPANCIES.md`.

### 65.6 Validation

* `analysis/separable_component_check.py` (output: `analysis/separable_component_check_output.txt`)
  — 750 random component lists over `F₁₇ … F₃₁`: containment (C3) and the degree bound (C4) hold
  in every instance meeting the hypotheses; the bad locus is nonempty in 708 of them, so the
  checks are not vacuous.
* `analysis/separable_component_counterexample_search.py`
  (output: `analysis/separable_component_counterexample_output.txt`) — the hypothesis-dropping
  search described above.

Exact integer arithmetic over `F_q` only; no floating point in either script.

## 66. Good specialisation points: the separable-component route with no `x₀` assumed

`RequestProject/Root/CodingTheory/SeparableComponentSpecialisation.lean`.

§65 states the component hypotheses at an evaluation point `x₀` of the auxiliary variable `X`
supplied by the user of the bound.  This section removes that point: the hypotheses become the
*intrinsic* ones — each component separable in `Y` over `F(Z)(X)`, distinct components coprime
in `Y` over `F(Z)(X)` — and the existence of a good `x₀` is **derived** from an explicit
counting hypothesis on the size of the field.  This closes the half of D65.4 that was
previously left conditional.

### 66.1 The bivariate resultant of two components

`resBiv b₁ b₂ R₁ R₂ = Res_Y(R₁, R₂) ∈ F[Z][X]`, the companion of the existing `discBiv`:

* `resLine_eq_eval_resBiv` — `resLine b₁ b₂ x₀ R₁ R₂ = (resBiv b₁ b₂ R₁ R₂).eval (C x₀)`;
* `resBiv_ne_zero_of_resLine_ne_zero` — the intrinsic hypothesis is *weaker* than the pointwise
  one;
* `natDegree_resBiv_le` — `deg_X Res_Y(R₁,R₂) ≤ (b₁ + b₂)·d_X`.

`SeparableComponents.discBiv_ne_zero` and `SeparableComponents.resBiv_ne_zero` show every
component list of §65 satisfies the intrinsic hypotheses; `twoComponentWitness_discBiv_ne_zero`
and `twoComponentWitness_resBiv_ne_zero` instantiate them on the explicit witness
`(Y − Z)·(Y − Z²)`, so the intrinsic notion is not vacuous.

### 66.2 The counting lemma and the good specialisation point

* `exists_eval_C_ne_zero_of_sum_natDegree_lt` — a finite family of nonzero polynomials of
  `X`-degrees `≤ d i` over `F[Z]` has a common non-root `C x₀`, `x₀ ∈ F`, as soon as
  `∑ d i < |F|`.  (Product of the family is nonzero, its degree is at most the sum, and the map
  `x₀ ↦ C x₀` is injective into the roots.)
* `exists_good_specialisation` — if all `discBiv (b i) (R i) ≠ 0`, all
  `resBiv (b i) (b j) (R i) (R j) ≠ 0` for `i ≠ j`, all coefficient `X`-degrees are `≤ d_X`, and

      ∑_{i ∈ s} (2b_i − 1)·d_X + ∑_{(i,j) ∈ s.offDiag} (b_i + b_j)·d_X < |F| ,

  then a single `x₀ : F` makes *every* component discriminant and *every* pairwise resultant a
  nonzero polynomial in `Z`.  `SeparableComponents.ofBivariate` packages the resulting record.

### 66.3 The bad-set bound with intrinsic hypotheses

* `card_badSet_le_affineSplit_componentsBiv`, `epsMCA_le_affineSplit_componentsBiv` — the summed
  bound of §65.3 with no `x₀` in the hypotheses, under the counting hypothesis above.

### 66.4 Post-Johnson under the explicit counting hypothesis

`SeparableComponentSplitBiv r h a` is the §65.4 hypothesis with (i) the component conditions
taken over `F(Z)(X)` and (ii) the field-size input replaced by the explicit counting hypothesis
`(2a³ + 2a⁴)·K⁵ < |F|`, which is exactly what the schedule budgets need for
`exists_good_specialisation` (`sum_component_degrees_le`).  Under it:

* `card_badSet_postJohnson_separableBiv` — `|bad| ≤ (a·r + 2a³ + 2a⁴)·K⁶`;
* `ordinaryRS_badSet_postJohnson_separableBiv` — the `∃ C` form;
* `ordinaryRS_epsMCAmax_postJohnson_separableBiv` — the `ε_mca` form `≤ C·K⁶/|F|`;
* `separable_prize_certificate_biv` — the `2⁻¹²⁸` certificate; the field-size requirement is the
  maximum of `(2a³ + 2a⁴)·K⁵ < |F|` and `2¹²⁸·C·K⁶ ≤ |F|`, and at `r = 2`, `K = 2¹⁸` the second
  dominates, so the certificate of §65.4 (`|F| ≥ 2²³⁶·C`) is unchanged.

The constant `C = a·r + 2a³ + 2a⁴` is therefore unchanged by the removal of `x₀`: the counting
hypothesis is a lower-order (`K⁵`) requirement.

### 66.5 Validation

`analysis/good_specialisation_check.py`
(output: `analysis/good_specialisation_check_output.txt`) — exact arithmetic over
`F₇ … F₂₃`, no floats, in the full three-variable model `F_q[Z][X][Y]`.  175 accepted random
instances (65 skipped because a degree bound reached `q`, where the grid zero-test would be
unsound).  In every one:

* the bad `X`-locus is contained in the degree bound, both in the sharper unordered-pairs form
  and in the ordered-pairs form actually proved in Lean;
* a good specialisation point exists whenever the bound is `< q`;
* end-to-end, at the first good `x₀` the bad-`z` containment and the `Z`-degree bound of §65
  hold for the specialised list.

The bad `X`-locus is nonempty in 27 of the 175 instances, so the containment check is not
vacuous.

## 67. The BCHKS25 separable factorisation of the interpolant, proved

Files: `RequestProject/Root/CodingTheory/FactorDegreeBounds.lean`,
`SeparableFactorisation.lean`, `SlackInterpolantSeparability.lean`,
`SquarefreeInterpolantPostJohnson.lean`.

The structural input of §66 (`SeparableComponentSplitBiv`: an affine split together with a
list of separable, pairwise coprime components carrying discriminant and resultant
certificates) is no longer assumed.  It is now *derived* from unique factorisation in
`F[Z][X][Y]`, Gauss's lemma over the function field `F(Z, X)`, and an explicit
characteristic hypothesis.

### 67.1 Degrees of a divisor (`FactorDegreeBounds.lean`)

* `coeff_coeff_swap`, `natDegree_swap_le_iff`, `swapZX`, `ZdegLe_iff_swap` — the coordinate
  description of `Polynomial.Bivariate.swap` and the `Z ↔ X` exchange for trivariates;
* `natDegree_le_of_dvd_trivariate`, `coeff_natDegree_le_of_dvd_trivariate`, `ZdegLe_of_dvd`
  — a divisor of `Q ≠ 0` inherits every per-variable degree budget of `Q`.  This is what
  gives the components of the factorisation the schedule budgets of the interpolant.

### 67.2 Gauss's lemma and the two certificates (`SeparableFactorisation.lean`)

* `FracZX F = Frac(F[Z][X]) = F(Z, X)`, `toFracZX`, `toFracZX_injective`;
* `isPrimitive_of_irreducible`, `irreducible_map_toFracZX` — an irreducible trivariate of
  positive `Y`-degree stays irreducible over `F(Z, X)`;
* `isCoprime_map_of_not_associated` — distinct irreducible factors are coprime there;
* `discBiv_ne_zero_of_map_irreducible` — the separability certificate: an irreducible factor
  whose `Y`-degree is prime to the characteristic has `discBiv ≠ 0`
  (`Polynomial.separable_iff_derivative_ne_zero` + `natDegree_derivative_eq_of_natCast_ne_zero`);
* `resBiv_ne_zero_of_map_isCoprime` — the coprimality certificate.

### 67.3 The factorisation theorems

* `exists_irreducible_factorisation` — for every nonzero `Q ∈ F[Z][X][Y]`,

      Q = C(X, Z) · ∏_{R ∈ s} R ^ e R ,

  with the `R` pairwise non-associated irreducibles of positive `Y`-degree, `e R ≥ 1`.
  This is the BCHKS25 §3.2 decomposition; it needs no hypothesis at all beyond `Q ≠ 0`.
* `SeparableInY`, `IsCoprimeInY`, `separableInY_iff_derivative_ne_zero`,
  `separableInY_of_irreducible`;
* `no_inseparable_factor_of_natDegree_lt_ringChar` — every irreducible factor of positive
  `Y`-degree of a `Q` with `deg_Y Q < ringChar F` is separable in `Y`;
* `SeparableFactorisation Q` (structure) and `exists_separable_factorisation` — the full
  BCHKS25 statement: content, irreducible factors with multiplicities, each separable in `Y`
  and pairwise coprime in `Y`, under the single hypothesis `deg_Y Q < ringChar F`;
* `exists_separable_components_of_squarefree` — for a *squarefree* `Q` the factorisation is
  multiplicity-free, so it is exactly the component list required by
  `card_badSet_le_affineSplit_componentsBiv`, with both certificates and with the degree
  budgets inherited by §67.1.

### 67.4 The concrete interpolant (`SlackInterpolantSeparability.lean`)

* `exists_minimal_lineInterpolant` — the "minimality field" is free: if the interpolation
  step has a solution it has one of least `Y`-degree (well-ordering of `ℕ`), so minimality
  never has to be added as an assumption;
* `no_inseparable_factor_of_slack` — for every `LineInterpolant k L m bY dZ D f₀ f₁ Q` with
  `bY < ringChar F`, every irreducible factor of positive `Y`-degree of `Q` is separable
  in `Y`;
* `exists_separable_factorisation_of_lineInterpolant` — the BCHKS25 factorisation for the
  concrete interpolant, under the same explicit characteristic hypothesis.

### 67.5 The post-Johnson chain (`SquarefreeInterpolantPostJohnson.lean`)

`SquarefreeInterpolantSplit r h a` replaces `SeparableComponentSplitBiv r h a`: it assumes
*no factorisation data whatsoever* — no affine split, no components, no discriminants, no
resultants — only that the interpolation step returns an interpolant `Q` at the post-Johnson
radius which is squarefree, of positive `Y`-degree, and inside the schedule budgets
`deg_Y Q ≤ a·K`, `deg_Z Q ≤ a·K²`, `deg_X Q ≤ a·K²`.  Under it, together with the explicit
characteristic hypothesis `a·K < ringChar F` and the explicit counting hypothesis
`(2a³ + 2a⁴)·K⁵ < |F|`:

* `card_badSet_postJohnson_squarefree` — `|bad| ≤ (2a³ + 2a⁴)·K⁶`;
* `ordinaryRS_badSet_postJohnson_squarefree` — the `∃ C` form;
* `ordinaryRS_epsMCAmax_postJohnson_squarefree` — `ε_mca ≤ C·K⁶/|F|`;
* `squarefree_prize_certificate` — the `2⁻¹²⁸` certificate.

The constant is *smaller* than in §66 (`2a³ + 2a⁴` instead of `a·r + 2a³ + 2a⁴`) because no
affine factors are peeled off.

### 67.6 What is refuted

* `not_isPow_of_irreducible` — an irreducible element is never a proper power, so the step
  "inseparable irreducible `R` ⟹ `R = S ^ p`" of the proposed minimality argument is
  contradictory as stated;
* `exists_expand_of_not_separableInY` — what zero derivative really gives is
  `R = expand p S`, i.e. `R ∈ F(Z, X)[Y^p]`, which is *not* a power statement (the
  coefficient field `F(Z, X)` is imperfect);
* `inseparableWitness = Y^p − Z`, `inseparableWitness_irreducible` (Eisenstein at the prime
  `Z` of `F[Z][X]`), `inseparableWitness_not_separableInY`,
  `exists_irreducible_not_separableInY`, `not_forall_inseparableInY_isPow` — in
  characteristic `p` an irreducible inseparable factor genuinely exists, so the
  characteristic hypothesis `deg_Y Q < ringChar F` cannot be dropped and cannot be replaced
  by minimality of `Q`.

### 67.7 Validation (exact arithmetic, no floats)

* `analysis/factorisation_slack_Q_check.py`
  (`analysis/factorisation_slack_Q_check_output.txt`) — 185 interpolants of real lines over
  `F₁₀₁`/`F₁₂₇`: `deg_Y Q < char` in 185/185; **no** inseparable factor below the
  characteristic (0/185, as the Lean theorem predicts); `Q` squarefree in `Y` over
  `L = F_q(Z)(X)` in 181/185, and the same for the residual after the affine split.  Four
  instances are non-squarefree with no correlated agreement.
* `analysis/inseparable_factor_slack_check.py`
  (`..._output.txt`) — Part A: `Y^p − Z` has vanishing `Y`-derivative and
  `deg gcd_Y(R, ∂R) = p` for `p = 2, 3, 5, 7`, and is not a `p`-th power; Part B: for
  `char = 5`, `(Y⁵ − Z)·Q₀` is still an interpolant and carries the inseparable factor
  (`deg gcd_Y = 5`); Part C: 172 interpolants over `F₅, F₇, F₁₁, F₁₃`, none inseparable
  while `deg_Y Q < char`.
* `analysis/lexicographic_minimality_check.py` (`..._output.txt`) — 20 instances: the
  concrete interpolant has minimal `Y`-degree in 20/20 (full lexicographic minimality in
  16/20; the four failures are `X`-degree improvements at equal `Y`-degree, irrelevant
  here), `deg_Y Q < char` in 20/20, squarefree in 18/20.  Minimality bounds the `Y`-degree —
  which is what makes the characteristic hypothesis free — but does not give squarefreeness.

### 67.8 Repeated affine factors allowed (`AffineSquarefreePostJohnson.lean`)

Guruswami–Sudan interpolation with multiplicity `m` normally produces an interpolant in
which a codeword line `Y − (A(X) + Z·B(X))` occurs with multiplicity up to `m`, so demanding
that `Q` itself be squarefree is stronger than needed.
`AffineSquarefreeInterpolantSplit r h a` only asks for

    Q = (∏ over a multiset of affine linear factors) · R,   R squarefree,

with `#Pairs ≤ a·K` and the schedule budgets on `R`; multiplicities among the affine factors
are unrestricted.  Under the same explicit hypotheses `a·K < ringChar F` and
`(2a³ + 2a⁴)·K⁵ < |F|`:

* `card_badSet_postJohnson_affineSquarefree` — `|bad| ≤ (a·r + 2a³ + 2a⁴)·K⁶`;
* `ordinaryRS_badSet_postJohnson_affineSquarefree` — the `∃ C` form;
* `ordinaryRS_epsMCAmax_postJohnson_affineSquarefree` — the `ε_mca` form.

The affine multiplicities cost only the affine term `#Pairs·|D| ≤ a·r·K²` of the bound, so
the constant is the §66 constant `a·r + 2a³ + 2a⁴` again.  What is still assumed is
multiplicity-freeness of the *non-affine* part — the case `e_i > 1` of D67.4.

## 68. Multiplicity elimination: the double-root carrier replaces squarefreeness

The last hypothesis of §67 was squarefreeness of the non-affine part of the interpolant
(D67.4, the case `e_i > 1`), the step BCHKS25 delegates to [BCI⁺20, Appendix C].  This
section replaces it with a strictly weaker hypothesis, proves the resulting post-Johnson
chain, and records two refutations that fix exactly how far the mechanism can go.
Files: `RequestProject/Root/CodingTheory/MultiplicityElimination.lean`,
`RequestProject/Root/CodingTheory/MultiplicityEliminationPostJohnson.lean`.

### 68.1 T1 — the multiplicity criterion

* `dvd_derivative_of_sq_dvd` — `R² ∣ Q → R ∣ ∂Q` over any commutative ring.
* `not_separable_of_sq_dvd` — a non-unit repeated factor destroys separability.
* `sq_dvd_iff_not_separable` — the converse holds over a **perfect** field:
  `(∃ R, ¬IsUnit R ∧ R² ∣ Q) ↔ ¬ Squarefree Q` in the `PerfectField` setting.

The `PerfectField` hypothesis is not decoration.  The requested unrestricted iff
`(∃ R, R² ∣ Q) ↔ gcd_Y(Q, ∂_Y Q) ≠ 1` is **false** over the coefficient field `F(Z)(X)`
actually in play (it is imperfect in characteristic `p`: `Y^p − Z` has vanishing derivative
and is irreducible), which is why the criterion is stated in the separability form.

### 68.2 T2 — specialisation preserves the square

* `sq_dvd_map_of_sq_dvd` — divisibility by a square is preserved under any coefficient
  ring hom applied coefficientwise.
* `sq_dvd_specZ_of_sq_dvd` — the instance for `Z ↦ z`: `P² ∣ Q → (specZ z P)² ∣ specZ z Q`.

### 68.3 The carrier hypothesis, replacing squarefreeness

    DoubleRootTransfer k R S :=
      ∀ z p,  deg p < k →  (Y − p)² ∣ R|_{Z=z}  →  (Y − p)² ∣ S|_{Z=z}

`S` is a *carrier* of the double roots of `R`.  This is weaker than squarefreeness of `R`:
`doubleRootTransfer_self` gives it for `S = R`, and `doubleRootTransfer_of_forall_not_dvd`
gives it whenever `R = G·S` and no candidate witness `Y − p` (`deg p < k`) divides any
specialisation of the repeated part `G` — proved through `sq_dvd_right_of_prime`
(`u` prime, `u² ∣ G·S`, `u ∤ G` ⇒ `u² ∣ S`) and `prime_X_sub_C_poly`.

### 68.4 The bad-set bound with arbitrary multiplicities

`card_badSet_le_affineSplit_transfer` — with the affine factors split off,

    |bad(k,e)| ≤ #Pairs·|D| + (b_S + (b_S − 1))·d_S ,

where the discriminant is taken of the **carrier** `S`, not of the residual `R`.  Nothing at
all is assumed about the multiplicities of the irreducible factors of `R`; with `S = R` the
statement degenerates to the §67 bound `card_badSet_le_affineSplit`.

Reassembled over a component list in
`card_badSet_le_affineSplit_components_transfer` and
`card_badSet_le_affineSplit_componentsBiv_transfer`.

### 68.5 The post-Johnson chain, same constants

`TransferInterpolantSplit r h a` asks, for every line, for an interpolant `Q` **and** a
squarefree carrier `S` of its double roots inside the schedule budgets.  `Q` itself is not
assumed squarefree and its factors may have arbitrary multiplicities.

* `transferInterpolantSplit_of_squarefreeInterpolantSplit` — the hypothesis is implied by
  the §67 hypothesis, so this is a strict weakening;
* `card_badSet_postJohnson_transfer` — `|bad| ≤ (2a³ + 2a⁴)·K⁶`, the §67 constant unchanged,
  under `a·K < ringChar F` and `(2a³ + 2a⁴)·K⁵ < |F|`;
* `ordinaryRS_badSet_postJohnson_transfer` (the `∃ C` form),
  `ordinaryRS_epsMCAmax_postJohnson_transfer` (the `ε_mca` form),
  `transfer_prize_certificate` (the `2⁻¹²⁸` form).

### 68.6 Refutation 1 — the reduced part is not a carrier

The obvious candidate for `S` is the reduced part `R / gcd_Y(R, ∂_Y R)`.  It does **not**
work: `doubleRootTransfer_reducedPart_fails` proves, from the explicit witness
`R = (Y − Z²)²` with reduced part `S = Y − Z²`, that

    ¬ DoubleRootTransfer k ((sqWitness F)^2) (sqWitness F)   for  1 ≤ k,

via `sq_dvd_specZ_sqWitness_sq` and `not_sq_dvd_specZ_sqWitness`.  So the carrier must be
supplied by the interpolation construction; it cannot be manufactured by squarefree
reduction.

The exact-arithmetic search agrees: `analysis/multiplicity_elimination_counterexample_search.py`
found **8 counterexamples in 120 scanned instances** in which `gcd_Y(R, ∂_Y R)` is nontrivial
but the `Z`-roots of the discriminant of the reduced part miss bad parameters — all of shape
`deg_Y R = 2`, `deg_Y R_red = 1` (i.e. `R = c·S²`).  A concrete one: `q = 101`, `n = 8`,
`k = 2`, `t = 6`, `m = 2`, `L = 11`, `D = [1..8]`,
`f₀ = [23,7,34,83,45,0,56,11]`, `f₁ = [55,37,4,6,54,79,8,28]`, bad set `{0,48,50}`; each bad
`z` has multiplicity 2 in `R_z` and 1 in `R_red,z`.

### 68.7 Refutation 2 — the line trace is vacuous on a genuine interpolant

The other natural route is to count bad `z` through the *line trace*

    lineTrace Q g₀ g₁ x  :=  Z ↦ Q(x, g₀(x) + Z·g₁(x)) ,

a univariate polynomial in `Z` for each position `x`.  `eval_lineTrace` computes it,
`lineTrace_eq_eval_atX` identifies it with the `atX` specialisation, `natDegree_lineTrace_le`
bounds its degree by `d_Z + b_Y`, and `eval_lineTrace_eq_zero_of_dvd` shows any witness makes
it vanish.  `card_badSet_le_lineTrace` then bounds

    |bad(k,e)| ≤ #Pairs·|D| + |U|·(d_Z + b_Y) ,   U := { x ∈ D : lineTrace ≠ 0 } ,

provided `|D \ U| + e < |D|`.

That proviso is exactly what fails.  `lineTrace_eq_zero_of_lineInterpolant` proves that a
genuine `LineInterpolant` has **vanishing trace at every position of `D`** — the
interpolation condition forces it — so `U = ∅` for `Q` and the counting hypothesis is
unsatisfiable.  The exact-arithmetic run
`analysis/multiplicity_elimination_check.py` confirms the residual behaves the same way:
`traceQ_zero` 66/66 and `|U| = 0` in 66/66 instances (`nondeg 0/66`), with the residual
non-squarefree in 27/66.

### 68.8 Honest status

The mechanism is **not** unconditional.  What is proved is that the squarefreeness of the
interpolant can be traded for the existence of a squarefree double-root carrier, at no cost
in the constants, and that the two constructions that would supply such a carrier for free
(squarefree reduction; line-trace counting) both fail.  The conditional frontier therefore
stands, now at `TransferInterpolantSplit` instead of `SquarefreeInterpolantSplit`.

### 68.9 The unconditional dichotomy: `codewordLocus` is the whole remaining obstruction

The carrier hypothesis of §68.3–68.5 can be traded for an *unconditional* theorem that names
the missing quantity.  For a factorisation of the residual `R = G·S` — no hypothesis
whatsoever on multiplicities — define the **codeword locus** of the repeated part,

    codewordLocus k G  :=  { z ∈ F : ∃ p, deg p < k and (Y − p) ∣ G|_{Z=z} } .

`card_badSet_le_repeatedPart` then proves, unconditionally,

    |bad(k,e)|  ≤  #Pairs·|D|  +  (b_S + (b_S − 1))·d_S  +  |codewordLocus k G| ,

needing only `discLine S ≠ 0` — asked of the surviving part `S`, not of `R`.  The proof is a
three-way split of every bad parameter: its witness is one of the split-off affine pairs, or
it is a genuine double root of `S|_{Z=z}` (caught by the discriminant, via
`sq_dvd_right_of_prime`), or it is a root of the repeated part `G|_{Z=z}`.

* `codewordLocus_one` and `card_badSet_le_repeatedPart_one` — for `G = 1` the third term is
  zero and the statement is exactly the `AffineFactorSplit` bound, so nothing is lost;
* `doubleRootTransfer_of_codewordLocus_eq_empty` — an empty codeword locus is precisely the
  carrier hypothesis, so the dichotomy and §68.4 are two views of the same split.

This is the sharpest honest form of the result: the entire content of [BCI⁺20, Appendix C]
that this project still lacks is a bound on `|codewordLocus k G|` for the repeated part of the
concrete Guruswami–Sudan interpolant.  Note that no purely algebraic bound can exist: for
`G = Y − Z²` the locus is all of `F` (the constant `p = z²` is a root at every `z`), so any
bound must use the agreement/decoding side of the argument, not gcd, derivative, resultant or
degree data alone.  That is exactly the shape of the counterexamples found numerically.

## 69. Unique decoding by double counting: the bad set of a line has at most `e + 1` points, and the literal `#bad ≤ 1` is false

`RequestProject/Root/CodingTheory/UniqueDecodingMCA.lean`.  This section is independent of
the whole interpolant machinery of §§62–68: no parametric list over `F(Z)`, no interpolant,
no multiplicity, no discriminant.  Only finite double counting on pairs `(γ, x)` with
`γ ∈ F` and `x ∈ D`.

### 69.1 Two good parameters already force correlated agreement

`exists_correlatedAgreement_of_two_goodZ` restates the two-point pencil argument in the shape
that the counting needs.  If `z₁ ≠ z₂` are both `e`-close, with local witnesses `p₁, p₂` of
degree `< k`, then

    q₁ := (p₁ − p₂)/(z₁ − z₂),   q₀ := p₁ − z₁·q₁

satisfy `deg q₀, deg q₁ < k` and

    |D| ≤ |polyAgreement f₀ q₀ ∩ polyAgreement f₁ q₁| + 2e .

There is no hypothesis on the radius and no list decoding: the two witnesses are *solved for*
the pair, not selected from a list.

### 69.2 A bad parameter must leave the common agreement set

`exists_mem_polyAgreement_sdiff_of_isBad`.  Write `T` for the common agreement set of §69.1
and, for a parameter `γ`, `A γ` for the agreement set of the line word `f₀ + γ·f₁` with
`q₀ + γ·q₁`.  In the regime `3e < |D| − k + 1` the uniqueness lemma
`eval_eq_add_smul_of_close` identifies *every* local witness at a good `γ` with `q₀ + γ·q₁`.
If a bad `γ` had `A γ ⊆ T`, then its badness witness set `S₀` would be contained in `T`, and
`(q₀, q₁)` would explain `f₀` and `f₁` simultaneously on `S₀` — that is `LineCloseOn`, which
badness forbids.  So `A γ \ T ≠ ∅`.

### 69.3 The private parts are disjoint, and the count closes

If a position `x` lay in `A γ \ T` and in `A γ' \ T` for `γ ≠ γ'`, then the two linear
equations in `(f₀ x, f₁ x)` are independent and force `f₀ x = q₀(x)`, `f₁ x = q₁(x)`, i.e.
`x ∈ T` (`mem_inter_polyAgreement_of_mem_two`).  Hence the sets `A γ \ T`, `γ` bad, are
pairwise disjoint subsets of `D \ T`.  Writing `c = #bad` and `u = |D| − |T|`:

* each private part is nonempty, so `c ≤ u`;
* each has `|A γ \ T| ≥ |D| − e − |T| = u − e`, so `c·(u − e) ≤ u`.

If `c ≥ e + 2` then `u ≥ c ≥ e + 2`, so `u − e ≥ 2`, and
`u ≥ c·(u − e) ≥ (e+2)·(u−e) = e·(u−e) + 2·(u−e) ≥ 2e + 2·(u−e) = 2u`, forcing `u = 0` —
contradicting `u ≥ e + 2 ≥ 2`.  Therefore

    card_badSet_le_succ_radius :   3e < |D| − k + 1  ⟹  #bad(k,e) ≤ e + 1 ,

which improves the previous count `#bad ≤ |D|` of `card_badSet_le` in the *same* regime, and
in density form

    epsMCA_le_succ_radius,  epsMCAmax_le_succ_radius :   ε_mca ≤ (e + 1)/|F| .

### 69.4 The literal claim `2e < |D| − k ⟹ #bad ≤ 1` is false

`not_forall_card_badSet_le_one` refutes it with a fully explicit, kernel-checked witness.
Over `F₇` with `D = F₇` (so `|D| = 7`), `k = 2`, `e = 1` — hence `2e = 2 < 5 = |D| − k` —
take

    w₀ = 1_{1} + 1_{2} ,   w₁ = 1_{1} + 2·1_{2} .

At `γ = 6` the line word vanishes on `S = D \ {2}` (`1 + 6·1 = 0` at the position `1`), and at
`γ = 3` it vanishes on `S = D \ {1}` (`1 + 3·2 = 0` at the position `2`).  Both `S` have
`|S| = 6 = |D| − e`, so the zero polynomial witnesses closeness of the line word.  But
`(w₀, w₁)` is *not* jointly explainable on either `S`: the five positions of
`Zw = D \ {1,2}` carry `w₀ = 0`, and `5 ≥ k = 2` zeros already force a degree-`< 2`
explanation of `w₀` to be the zero polynomial on all of `D`
(`eval_eq_of_card_agreement_ge`), contradicting `w₀ = 1` at the position that survives in `S`.
So both `3` and `6` are bad and `#bad ≥ 2`.

Since `e + 1 = 2` for this instance, the same witness shows that `card_badSet_le_succ_radius`
is **sharp**: the bound `e + 1` cannot be replaced by anything smaller.

### 69.5 Validation

Exact arithmetic modulo a prime, no floats.

* `analysis/unique_decoding_two_good_check.py` — 180 instances, `q ∈ {7,11,13}`,
  `N ∈ {5,6,7}`, `k ∈ {2,3}`: 0 failures of the two-point correlated-agreement claim, 0
  failures of `#bad ≤ e+1` in the regime `3e < N−k+1`, **21** failures of the literal
  `#bad ≤ 1`, and the value `e+1` is attained in 33 instances.
* `analysis/unique_decoding_two_good_counterexample_search.py` — 826 instances: `S1 = 0`
  (two-point correlated agreement never fails), `S2 = 112` (refutations of `#bad ≤ 1`),
  `S3 = 0` and `S4 = 0` (no violation of `#bad ≤ e+1`, inside or outside the `3e` regime).
  Largest bad set observed: `3` in the `3e` regime, `3` in the `2e`-only regime, `6` outside.

All eight new declarations are audited in `RequestProject/Main.lean` and depend only on
`[propext, Classical.choice, Quot.sound]`.

## 70. The `3e` hypothesis of the unique-decoding anchor theorem is optimal

New file: `RequestProject/Root/CodingTheory/UniqueDecodingGapWitness.lean`
(imported and audited from `RequestProject/Main.lean`).

### 70.1 The question

`card_badSet_le_succ_radius` (§69) proves `#bad ≤ e + 1` under `1 ≤ k ≤ |D|` and
`3e < |D| − k + 1`.  The question put to this run was whether the hypothesis may be weakened
to the unique-decoding condition `2e < |D| − k + 1` while keeping the conclusion.

### 70.2 Answer: no, and in the strongest possible way

`not_forall_card_badSet_le_succ_radius_of_two_radius` refutes the weakened statement with an
explicit, kernel-checked witness.  Over `F₅` with `D = {0,1,2,3}` (so `|D| = 4`), `k = 2`,
`e = 1` — hence `2e = 2 < 3 = |D| − k + 1`, while `3e = 3` is *not* `< 3` — take

    g₀ = 1_{1} ,   g₁ = 1_{0} + 1_{1} .

The four parameters `0, 2, 3, 4` are all bad (`GapWitness.isBad_zero`, `isBad_two`,
`isBad_three`, `isBad_four`), so `#bad ≥ 4 = |D| > e + 1 = 2`
(`GapWitness.four_le_card_badSet`).  The local witnesses are

| `γ` | witness set `S` | codeword on `S` | obstruction to `LineCloseOn` |
|-----|-----------------|-----------------|------------------------------|
| `0` | `{0,2,3}`       | `0`             | `g₁` vanishes at `2,3`, not at `0` |
| `2` | `{0,1,3}`       | `X + 2`         | `g₀` vanishes at `0,3`, not at `1` |
| `3` | `{0,1,2}`       | `X + 3`         | `g₀` vanishes at `0,2`, not at `1` |
| `4` | `{1,2,3}`       | `0`             | `g₀` vanishes at `2,3`, not at `1` |

Two consequences, both stronger than the bare refutation:

* since `#bad = |D|`, in the band `2e < |D| − k + 1 ≤ 3e` **no** bound of the form
  `#bad ≤ c(e)` can hold — the trivial bound `card_badSet_le` is attained;
* the mechanism is visible: at `γ = 2, 3` the line word is close to a *nonzero* codeword,
  which is possible exactly when `|D| − 3e ≤ k − 1`, i.e. exactly in the band.

Two reusable lemmas were extracted: `not_lineCloseOn_of_fst_zero_set` and
`not_lineCloseOn_of_snd_zero_set` — if one coordinate of the pair vanishes on `k` positions
of `S` and is nonzero somewhere on `S`, the line is not close on `S`.

### 70.3 The refined boundary, and the interface to the Welch–Berlekamp pencil

Every counterexample found (exhaustively, §70.4) satisfies `2e = |D| − k` exactly.  The
strictly stronger hypothesis `k + 2e < |D|` — the regime of `WelchBerlekampPencil.lean` — is
*not* refuted.  Accordingly the two unique-decoding criteria are now combined:

    card_badSet_le_succ_radius_of_count_or_pencil :
        3e < |D| − k + 1  ∨  (∃ ρ, wbDet k e f₀ f₁ ρ ≠ 0)   →   #bad ≤ e + 1 .

The witness lies outside both branches: it has `k + 2e = |D|`, and
`GapWitness.wbDet_eq_zero` shows every maximal minor of its pencil vanishes identically.  So
the only statement left open in the whole unique-decoding range is

> `k + 2e < |D|` together with a totally degenerate pencil ⟹ `#bad ≤ e + 1`.

### 70.4 Validation (exact arithmetic, no floats)

* `analysis/badset_2e_common.py` — engine for the strong bad set; the scans are exhaustive up
  to two *theorems*: invariance of `badSet` under subtracting a codeword pair and under global
  scaling, and the fact (`exists_correlatedAgreement_of_two_goodZ`, no radius hypothesis) that
  two good parameters produce a codeword pair agreeing with `(f₀,f₁)` on `≥ |D| − 2e`
  positions, so any instance with `#bad ≥ 2` has a representative supported on `≤ 2e` points.
* `analysis/badset_2e_condition_check.py` (+ saved output) — Phase 0 (the three small mission
  instances, all of which satisfy `3e < |D| − k + 1` and therefore cannot refute anything),
  Phase 1 (audit of the anchor theorem: 1 200 036 instances in the regime `3e < |D| − k + 1`,
  **0** violations), Phase 2 (gap regime: refuted for every scanned tuple, with
  `max #bad = |D|` throughout).
* `analysis/badset_2e_condition_counterexample_search.py` (+ saved output) — minimal
  counterexamples for `q ∈ {5,7,11,13}`; every bad set is recomputed by the independent
  Lagrange-based implementation of `unique_decoding_two_good_check.py` and agrees.
* `analysis/badset_wb_regime_probe.py` (+ saved output) — the strict window `k + 2e < |D|`:
  exhaustive where feasible (`q=7`, `|D|=6`, `k=1`, `e=2`: 14 412 000 instances,
  `max #bad = 3 = e+1`), plus random, planted and rational lines for larger fields.
* `analysis/badset_smooth_domain_probe.py` (+ saved output) — multiplicative-subgroup and
  coset domains behave exactly like generic ones (`max #bad = |D|` in the gap regime), so
  smoothness of the evaluation domain does not improve the line bad set.

All new declarations are audited in `RequestProject/Main.lean` and depend only on
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, no new axioms.

The strategic consequence — which route should now carry the proximity-gap effort — is
recorded in `MCA_ROUTE_DECISION.md`.

---

## 71. The strict unique-decoding window `k + 2e < |D|` — refuted

**Question (Strand 1).**  `card_badSet_le_succ_radius` gives `#bad ≤ e + 1` in the counting
regime `3e < |D| − k + 1`, and `UniqueDecodingGapWitness` refutes the boundary case
`k + 2e = |D|`.  Does the *strict* window `k + 2e < |D|` suffice?

**Answer: no.**  `RequestProject/Root/CodingTheory/StrictWindowRefutation.lean` gives an
explicit kernel-checked witness:

| item | value |
|------|-------|
| field | `ZMod 11` |
| domain `D` | `{0, 1, 2, 3, 4, 5, 9, 10}`, `|D| = 8` |
| `k`, `e` | `3`, `2` — so `k + 2e = 7 < 8 = |D|` (and `3e = 6 = |D| − k + 1`, just outside the anchor regime) |
| `f₀` | indicator of `{0, 3}` |
| `f₁` | `1` at `0` and `3`, `3` at `1` and `2`, `0` elsewhere |
| bad set | `{0, 1, 8, 10}`, so `#bad = 4 > 3 = e + 1` |

* `StrictWindowWitness.four_le_card_badSet` — the four bad parameters, each with an explicit
  witness set `S = D \ {·,·}` of size `6 = |D| − e` and an explicit local codeword (`0` for
  `γ ∈ {0, 10}`, the quadratics `5X²+7X+2` and `9X²+6X+9` for `γ ∈ {1, 8}`).
* `StrictWindowWitness.wbDet_eq_zero` — every maximal minor of the Welch–Berlekamp pencil of
  the witness vanishes, so the witness also escapes `card_badSet_le_of_wbDet_ne_zero`.  This
  closes the hole left open in the docstring of
  `card_badSet_le_succ_radius_of_count_or_pencil`: the strict window *plus* a degenerate
  pencil is not enough either.
* `not_forall_card_badSet_le_succ_radius_strict_window` — the strict-window statement is
  false as a theorem schema.

**Why blind scanning missed it.**  Writing `D = U ⊔ T` with `U` the joint support of the pair
(`|U| = 2e = 4`, legitimate by `exists_correlatedAgreement_of_two_goodZ` plus invariance of
`badSet` under subtracting a codeword pair) and `|T| = k + 1`, a bad parameter with a nonzero
local witness `p` must have `p = λ·∏_{y ∈ T \ {s,s'}}(X − y)`, and on `U` such a `p` is
proportional to the Cauchy difference `w_s − w_{s'}`, `w_s(x) = 1/(x − s)`.  So the bad
parameters are exactly the directions of the plane `span(f₀|U, f₁|U)` that are either Cauchy
differences (nonzero local witness) or vanish at two coordinates of `U` (zero local witness).
Cauchy nonsingularity forbids four `w_s` in one coset of the plane, and a residue computation
forbids a vanishing direction inside the plane of a Cauchy triple; but two **disjoint** pairs
plus two complementary vanishing directions give `4 > e + 1` bad parameters.  This needs
`k ≥ 3`, `|D| ≥ 8`, `q ≥ 8` — outside every earlier scan — and it is a codimension-2 event, so
random sampling essentially never meets it.

**Numerical validation (exact arithmetic, no floats, two independent engines).**

* `analysis/strict_window_common.py` — second engine: interpolation over `k`-subsets rather
  than enumeration of all `q^k` codewords.
* `analysis/strict_window_check.py` (+ saved output) — Phase 0 regime map (the strict window
  is testable only for `e ≥ 2`); Phase 1 exhaustive scan of the whole `F₇` gap regime
  (1 160 000 reduced instances, `max #bad = 3 = e + 1`, **0** violations); Phase 2 blind
  random scan at the smallest counterexample parameters (4 000 instances, 0 violations —
  documenting the rarity); Phase 3 the structural witness, both engines agreeing on
  `#bad = 4`.
* `analysis/strict_window_counterexample_search.py` (+ saved output) — the structural search:
  3 780 planes scanned at `q = 11`, `|D| = 8`, `k = 3`, `e = 2`, **252** counterexamples, each
  cross-checked by both engines.

**Consequence for the project.**  For the strong bad set the sharp count `#bad ≤ e + 1` is
governed by the counting hypothesis `3e < |D| − k + 1`, not by unique decoding: between
`k + 2e < |D|` and `k + 3e ≤ |D|` there are genuine lines with `e + 2` bad parameters.  The
conjecture recorded in earlier sessions is therefore closed as **false**, and no proof effort
should be spent on it.

---

## 72. The first concrete syndrome/MDS certificate at rate `ρ = 1/2`

**File.** `RequestProject/Root/CodingTheory/RhoHalfSyndromeCertificate.lean`.
**Scripts.** `analysis/rho_half_syndrome_mds_search.py`, `analysis/rho_half_upper_bound_check.py`
(both exact integer/`Fraction` arithmetic, no floating point; outputs saved next to them).

`CircuitIncidence.lean` proves the unconditional circuit-incidence (syndrome/MDS) bound

```
#bad · C(T − 1, a − 1) ≤ C(|D|, a),    T = max(|D| − e, k + 1),  k + 1 ≤ a ≤ T,
```

valid at every error budget — no Johnson, list-decoding or degeneracy hypothesis.  This
section turns it into a finite certificate at the parameters the mission asked for.

**Parameters.** `n = |D| = 2²⁰`, `k = 2¹⁹` (true rate `1/2`), `e = 314572`
(`δ = e/n = 0.2999992…`), test size `a = k + 1 = 524289`, `T = n − e = 734004`.  The test size
`a = k + 1` is optimal among the admissible ones (checked exactly: ratio bit lengths
415043 / 415045 / 415063 / 416398 / 512113 for `a = k+1, k+2, k+16, k+1024, k+65536`).

**Proved (kernel-checked, axioms `propext, Classical.choice, Quot.sound` only).**

* `choose_ratio_le_rho_half` — `C(2²⁰, 2¹⁹+1) ≤ 2⁶⁹⁹⁰⁵² · C(734003, 2¹⁹)`;
* `choose_ratio_ge_rho_half` — `2²⁰⁹⁷¹⁴ · C(734003, 2¹⁹) ≤ C(2²⁰, 2¹⁹+1)`;
* `circuit_field_size_ge_rho_half` — every constant that the circuit inequality can produce at
  these parameters is `≥ 2²⁰⁹⁷¹⁴`;
* `card_badSet_le_rho_half_circuit` — every line has at most `2⁶⁹⁹⁰⁵²` bad parameters at that
  radius;
* `epsMCAmax_le_rho_half_circuit` — **the certificate**: `ε_mca ≤ 2⁻¹²⁸` for every field with
  `|F| ≥ 2⁶⁹⁹¹⁸⁰`;
* `epsMCAmax_le_rho_half_counting` — the cheap rate-1/2 certificate: `δ = 1/6`
  (`e = 174762`), `|F| ≥ 2¹⁴⁶`;
* `epsMCAmax_le_rho_quarter_counting` — the mission's literal parameters (`k = 2¹⁸`, i.e.
  `ρ = 1/4`), `δ = 1/4`, `|F| ≥ 2¹⁴⁷`.

**The two-sided bracket.**  `[2²⁰⁹⁷¹⁴, 2⁶⁹⁹⁰⁵²]` for the constant of the route; the exact ratio
computed in exact integer arithmetic has bit length 415043, inside the bracket.  So the
bracket is genuine but not tight, and the *method* cannot certify `2⁻¹²⁸` with a field below
`2²⁰⁹⁸⁴²` at these parameters.

**Honest reading.**  `δ = 0.2999992…` exceeds the unique-decoding radius `1/4` and the Johnson
radius `1 − √(1/2) = 0.2928932…`; the price is an exponentially large field, so **no
post-Johnson and no capacity claim is made** — nothing here is a cryptographic parameter set.
The practically meaningful rate-1/2 statement is the counting one (`δ = 1/6`, `|F| ≥ 2¹⁴⁶`).

**Proof technique worth reusing.**  All the arithmetic goes through lemmas whose exponents are
*variables* (`upper_core`, `lower_core`, `le_two_pow_mul_of_two_pow_mul_le`,
`pow_mul_choose_le`), and each concrete step is a separate top-level theorem.  With numerals
such as `2^524288` in the goal, numeral-normalising tactics and a single large proof term both
fail (`maximum recursion depth`, `(kernel) deep recursion detected`); the split makes every
piece check comfortably.

---

## 73. Monomial packets: `#Bad ≤ 1` holds on one and two cosets, fails on three

**Scripts.** `analysis/multicoset_monomial_common.py` (a third independent exact engine for
the strong bad set, by enumeration of deleted positions), `analysis/multicoset_monomial_scan.py`,
`analysis/multicoset_monomial_control.py`, `analysis/multicoset_monomial_sharp_slice.py`.
**File.** `RequestProject/Root/CodingTheory/MulticosetMonomialWitness.lean`.

Exhaustive scan of two-layer **monomial** packets `f₀(t) = α t^{d₀}`, `f₁(t) = β t^{d₁}` on
domains that are unions of `s` cosets of a multiplicative subgroup, in the regime
`3e + k ≤ |D|` (the regime of `card_badSet_le_succ_radius`, where `#Bad ≤ e + 1` is proved):

| domain | instances | max `#Bad` | first `#Bad > 1` | first `#Bad > s` |
|---|---:|---:|---|---|
| one coset `H` | 14 167 | 1 | none | none |
| one coset, degenerate coefficients `(0,1),(1,0)` | 3 881 | 1 | none | none |
| two cosets `H ∪ cH` | 251 786 | 1 | none | none |
| three cosets `H ∪ cH ∪ c'H` | 1 849 491 | 3 | **yes** | none |

Total 2 119 325 instances, exact arithmetic, `q ∈ {5,…,31}`, all `N | q−1`, all coset
representatives, all exponents modulo `|D|`, all feasible `k, e`.  Engine cross-validation:
896 instances against the interpolation engine of `analysis/strict_window_common.py`, no
disagreement.

**Sensitivity control.**  `analysis/multicoset_monomial_control.py`: on the *same* domains and
in the *same* regime, random general (non-monomial) packets give the histogram
`#Bad ∈ {0: 1082, 1: 90, 2: 28}` over 1 200 instances, so the ceiling of `1` above is a
property of monomial packets, not blindness of the engine.

**Formalized negative result.**  `not_forall_monomial_card_badSet_le_one`: over `ZMod 13` with
`D = {±1, ±2, ±3}` (three cosets of `{±1}`), `k = 2`, `e = 1` (so `3e + k = 5 ≤ 6 = |D|`) and
the monomial packet `f₀ = t⁴`, `f₁ = t⁵`, the bad set is `{1, 12}`.  Certificates: for `γ = 1`,
`S = D∖{1}` and the codeword `3X + 3`; for `γ = 12`, `S = D∖{12}` and `10X + 3`; in both cases
`f₀ = 3` on `{2,3}` but `f₀ = 1` at the remaining point of `S`, which obstructs `LineCloseOn`
through the new reusable lemma `not_lineCloseOn_of_fst_const_set`.  Kernel-checked, axioms
`propext, Classical.choice, Quot.sound` only.

Note `#Bad = 2 = e + 1` there, so the general theorem is untouched: what is refuted is the
*monomial sharpening* beyond two cosets.  The weaker bound `#Bad ≤ s` survived every scanned
instance and remains **open**.

---

## 74. The structured second layer: `#Bad ≤ 1` from the degree of `f₁` alone

**File.** `RequestProject/Root/CodingTheory/StructuredSecondLayer.lean`.
**Script.** `analysis/structured_second_layer_check.py` (+ saved output; exact arithmetic).

All earlier `#Bad ≤ 1` statements in this project needed a hypothesis on *both* layers of the
line (the monomial packets of §73) or held only as the counting bound `#Bad ≤ e + 1` (§69).
The theorem of this section needs a hypothesis on the **second layer only**.

**Theorem (`card_badSet_le_one_of_structured_snd`).**  Let the second layer be the evaluation
on `D` of a single polynomial `g`, i.e. `f₁ x = g(x)` for every `x ∈ D`, and suppose

```
k ≤ deg g < t        and        2e + t ≤ |D|.
```

Then `#Bad ≤ 1` — **whatever `f₀` is**, and with no bound on `e` beyond `2e + t ≤ |D|`.
Consequently `ε_mca(line) ≤ 1/|F|` (`epsMCA_le_one_div_of_structured_snd`).

**Proof.**  Two distinct bad parameters give, by `correlated_agreement_of_two`, one *common*
set `T` of at least `|D| − 2e ≥ t` positions carrying a codeword pair `(q₀, q₁)`, `deg q₁ < k`.
Then `g − q₁` has degree `< t` and vanishes on `T`, so `g = q₁` and `deg g < k`, contradicting
`k ≤ deg g`.  Three lines of mathematics; the strength comes from the *window*, not from the
argument.

**The degree trichotomy.**  For `f₁` the evaluation of one polynomial `g`:

| regime | condition | bound | status |
|---|---|---|---|
| codeword | `deg g < k` | `#Bad = 0` | **proved** (`badSet_eq_empty_of_codeword_snd`) |
| structural | `k ≤ deg g < t`, `2e + t ≤ |D|` | `#Bad ≤ 1` | **proved** (`card_badSet_le_one_of_structured_snd`) |
| degenerate | `deg g ≥ t` | unbounded by `1` | **refuted** (§73 witness, and control B below) |

The codeword row is immediate once stated: `f₁` and hence `f₀` are close on any witness set,
so `line_closure` applies and no parameter can be bad.  The degenerate row is exactly where
the three-coset counterexample of §73 lives (`deg g = 5` there, while `t ≤ |D| − 2e = 4`),
which is why that instance is *not* a counterexample to the theorem above: the degree window
is essential, not decorative.

**Monomial corollary (`card_badSet_le_one_of_monomial_snd`).**  `f₁(x) = c·x^d`, `c ≠ 0`,
`k ≤ d < t`, `2e + t ≤ |D|` ⇒ `#Bad ≤ 1`.  This *proves* the ceiling that the exhaustive
monomial scans of §73 observed on one and two cosets, inside — and only inside — the window.

**Concrete `ρ = 1/2` certificate (`epsMCA_le_two_pow_neg_128_structured_rho_half`).**
`|D| = 2²⁰`, `k = 2¹⁹`, `e = 262143` (`δ = 262143/2²⁰ ≈ 0.2499990`), `f₁` the evaluation of a
polynomial of degree exactly `k`.  Then `ε_mca(line) ≤ 2⁻¹²⁸` for every field with
`|F| ≥ 2¹²⁸`.  Compared with the unstructured certificates of §72 at the same rate: radius
`≈ 0.25` instead of `1/6`, field `2¹²⁸` instead of `2¹⁴⁶`.

**Scope — read this before quoting the certificate.**  This is a bound on `ε_mca` of a *line
whose second layer satisfies the structural hypothesis*, not on `epsMCAmax` (the maximum over
*all* lines, which is what a protocol soundness proof needs when the prover is unrestricted).
Nothing post-Johnson and nothing about capacity is claimed: `δ < 1/4` is inside the
unique-decoding radius for `ρ = 1/2`.  What is new is that the *optimal* error `1/|F|` — not
`(e+1)/|F|` — is reached at essentially the full unique-decoding radius, with no hypothesis on
`f₀`.

**Numerical pre-verification.**  7 284 instances with the hypotheses satisfied: `max #Bad = 1`,
of which 3 753 attain `#Bad = 1` (so the bound is tight and the scan is not vacuous); control A
(`deg g < k`) gives `#Bad = 0` throughout its 2 046 instances; control B (`deg g ≥ t`) reaches
`#Bad = 10` over 3 662 instances.

---

## 75. The radix-2 (FRI) fold makes the structural hypothesis a statement about `deg P`

**File.** `RequestProject/Root/CodingTheory/FRIFoldStructured.lean`.

§74 assumes that the second layer is one polynomial.  Which protocols supply that?  This
section answers it for the generator of the FRI/STARK family, the **radix-2 fold**.

One FRI round splits the tested word `f` on a domain closed under `x ↦ −x` into

```
f(x) = f_even(x²) + x·f_odd(x²),
```

and runs the proximity test on the line `γ ↦ f_even + γ·f_odd` over the folded domain.  The
file defines the two layers literally in that form, through a square-root section `σ` of the
folded domain (`friFst`, `friSnd`; `exists_sqrt_section` shows the section exists for the
genuine FRI geometry, i.e. for a folded domain that is the squaring image of a domain avoiding
`0`), and proves:

* `friSnd_eval` — **if the tested word is the evaluation of one polynomial `P`, the second
  layer of its fold is the evaluation of one polynomial, namely `oddPart P`** (coefficients
  `(oddPart P).coeff j = P.coeff (2j+1)`).  So the structural hypothesis of §74 is *automatic*
  for a single-polynomial prover — it is not an extra assumption about the layer, it is a
  consequence of the fold;
* `friFst_eval` — the same for the first layer and `evenPart P` (not needed by the bound, but
  it makes the split complete);
* `degree_oddPart_lt` — `deg P < 2n ⇒ deg (oddPart P) < n`;
* `degree_oddPart_eq_of_natDegree` — `deg P = 2m+1 ⇒ deg (oddPart P) = m` exactly.

The trichotomy of §74 therefore becomes a condition on the degree of the prover's word:

| prover's word | fold's second layer | bound |
|---|---|---|
| `deg P < 2k` (a codeword of the pre-fold code) | `deg < k` | `#Bad = 0` (`fri_fold_badSet_eq_empty_of_low_degree`) |
| `deg P = 2m+1` with `k ≤ m < t`, `2e + t ≤ |D|` | `deg = m` in the window | `#Bad ≤ 1` (`fri_fold_card_badSet_le_one`), `ε_mca ≤ 1/|F|` (`fri_fold_epsMCA_le`) |
| `deg P ≥ 2t` | `deg ≥ t` | not bounded by `1`; only `#Bad ≤ e + 1` (§69) |

**Protocol-level certificate (`fri_round_epsMCA_le_two_pow_neg_128`).**  One FRI round at rate
`ρ = 1/2`: folded domain of size `2²⁰`, post-fold degree bound `k = 2¹⁹`, radius
`e = 262143` (`δ ≈ 0.2499990`), prover's word the evaluation of a single polynomial of degree
`2²⁰ + 1` — one above the pre-fold bound `2k = 2²⁰`, i.e. the cheapest possible cheating
degree.  Then the folded line has `ε_mca ≤ 2⁻¹²⁸` in every field with `|F| ≥ 2¹²⁸`,
independently of the first layer.

**Scope.**  The hypothesis is on the *prover's word*, namely that it is the evaluation of a
single polynomial of controlled degree.  A fully adversarial prover sends an arbitrary vector,
for which only `#Bad ≤ e + 1` is available; this section says precisely how much a
single-polynomial prover gains, and nothing more.  See §76 for what is still missing on the
*circle* side.

---

## 76. Interface audit: which of these applies to Circle-STARK

Re-audit of `CIRCLE_STARK_INTERFACE_AUDIT.md` against the state after §74–§75.

* **Univariate FRI: connected.**  The radix-2 fold is now defined inside the coding-theory
  development (§75), so the question "is `f₁` the evaluation of a single polynomial, and of
  what degree?" has a proved answer: yes for a single-polynomial prover, and the degree is
  `⌊(deg P − 1)/2⌋`.  The window `k ≤ deg g < t`, `2e + t ≤ |D|` is met exactly when
  `2k + 1 ≤ deg P ≤ 2t − 1` with `deg P` odd, and `fri_round_epsMCA_le_two_pow_neg_128`
  instantiates it.
* **Circle-STARK: still not connected, and the missing piece is unchanged.**  The circle
  development (`RequestProject/Circle*.lean`) defines the twin-coset domain `cpt` and the
  circle FFT, but *no circle code*: there is no definition of the space of functions on a
  twin coset obtained by evaluating `F[x,y]/(x²+y²−1)` in bounded degree, and hence no circle
  bad set to bound.  The failing condition is therefore not one of the degree inequalities —
  it is that the object the inequalities would speak about does not exist in the repository.
  The concrete missing structure, in order: (1) the circle code as a submodule of functions on
  `cpt`; (2) the 2-to-1 `x`-projection splitting it into even and odd univariate RS parts on
  the projected domain; (3) the identification of the circle fold's second layer with the odd
  part, which is where §75 would plug in verbatim.
* **Honest status.**  No Circle-STARK certificate is claimed.  The certificate that *is*
  proved is the univariate FRI-round one of §75.

---

## 77. The coset-count bound `#Bad ≤ s` is false

**File.** `RequestProject/Root/CodingTheory/MulticosetSharpSliceWitness.lean`.
**Scripts.** `analysis/multicoset_monomial_sharp_slice.py` (+ saved output),
`analysis/multicoset_sharp_slice_witness.py` (two independent exact engines).

§73 left open the weaker guess `#Bad ≤ s`, `s` = the number of cosets making up the domain.
The slice scan restricted to `e + 1 > s` — the only regime where the guess would say anything
beyond the proved `#Bad ≤ e + 1` — has now been completed for `q ∈ {5,…,29}`:

| `s` | instances in the slice | max `#Bad` | violations of `#Bad ≤ s` |
|---:|---:|---:|---:|
| 1 | 10 995 | 1 | 0 |
| 2 | 31 112 | 1 | 0 |
| 3 | 26 256 | **4** | **18** |

(The prime `q = 31` needs well over ten minutes on top of this and was not run; the script now
takes the prime list on the command line, and the recorded output is the completed
`q ∈ {5,…,29}` run.)

**Formalized refutation.**  `not_forall_monomial_card_badSet_le_three_cosets`: over `ZMod 17`
with `H = {1,4,13,16}` (the subgroup of order 4) and `D = H ∪ 2H ∪ 3H` (so `s = 3`,
`|D| = 12`), `k = 2`, `e = 3` — inside the regime, `3e + k = 11 ≤ 12` — and the monomial
packet `f₀ = t⁸`, `f₁ = t⁹`, the bad set is `{6, 7, 10, 11}`, so `#Bad = 4 > 3 = s`
(`MulticosetSharpSliceWitness.four_le_card_badSet`).

**Mechanism.**  `t⁸` is the quadratic character: `1` on the eight squares of `D`, `−1` on the
four non-squares `{3,5,12,14}`.  For each of the four bad `γ` take `S` = the squares plus the
single non-square `−1/γ`; on the squares the line reads `1 + γt`, and at `t = −1/γ` it reads
`−1 − γt = 0 = 1 + γt`, so the *linear* codeword `γX + 1` fits on all of `S`, while `f₀` alone
cannot (it is `1` on eight points and `−1` at the ninth).  Different `γ` retain different
non-squares, which is what produces four bad parameters.  Note `#Bad = 4 = e + 1`: the proved
bound is untouched and tight here.

**Consequence.**  The coset-count route is **closed**.  What survives from §73 is the
observation `#Bad ≤ 1` for one and two cosets in the scanned range, and that is now explained
— and proved, in the degree window — by §74: on a single coset a monomial reduces to an
exponent below the coset order, which is where the window `k ≤ d < t` is met.

---

## 78. Session closure: consolidated state, and the circle-code feasibility probe

This section closes the phase.  It adds no new Lean declaration; it records the consolidated
state and the outcome of one small, explicitly scoped feasibility question.

### 78.1 What stands at the close of the phase

| result | file | status |
|---|---|---|
| structured second layer, `#Bad ≤ 1` in the degree window (§74) | `StructuredSecondLayer.lean` | proved |
| FRI fold bridge: the fold's second layer *is* `oddPart P` (§75) | `FRIFoldStructured.lean` | proved |
| one-round certificate `ε_mca ≤ 2⁻¹²⁸` at `ρ = 1/2`, `δ ≈ 0.25` (§75) | `FRIFoldStructured.lean` | proved |
| coset-count bound `#Bad ≤ s` (§77) | `MulticosetSharpSliceWitness.lean` | refuted |
| Circle-STARK certificate (§76) | — | **open gap**, nothing claimed |

The whole repository builds (`lake build`, 8199 jobs, no error), contains no `sorry` and no
`admit` in any `.lean` file, and introduces no axiom beyond
`propext, Classical.choice, Quot.sound`.

The one-round certificate is unconditional *given the fold hypothesis*, i.e. given that the
prover's word is the evaluation of a single polynomial of the stated degree; §75 proves that
under that hypothesis nothing further about the second layer need be assumed.  It is a
statement about **one** round and about **one** line; no multi-round FRI certificate and no
bound on `epsMCAmax` over all lines is claimed anywhere.

### 78.2 The feasibility probe: how large is "define the circle code"?

The question asked was narrow: *can the circle code be defined in this repository in some 15–20
lines?*  The answer, checked by elaborating the candidate in a scratch file **and deliberately
not committed to the repository**, is:

* **The definition itself: yes, about a dozen lines.**  Using the existing `FFT.Circle`
  structure, the code on a domain `D : Finset (Circle F)` is the span of the restrictions of
  `a(x) + y·b(x)` with `deg a, deg b < k` — a `Submodule F (↥D → F)`, elaborating without
  incident.  The `x`-projection `D.image (·.x)` is one further line.
* **But the definition alone proves nothing**, and this is the substantive part of the answer.
  Two things carry all the content, and neither is short:
  1. a **minimum-distance bound** for that submodule (how many common zeros `a(x) + y·b(x)`
     can have on a twin coset).  This is what would make the code usable, because the
     alphabet-generic MCA layer already in the repository
     (`Root.CodingTheory.Alphabet.card_badSet_le`, `epsMCAmax_le`) applies to *any* submodule
     `C ⊆ (ι → A)` once `MinDistGe C d` and `3e < d` are available — so a circle code with a
     distance bound would immediately inherit `ε_mca ≤ n/|F|` with no new MCA theory;
  2. the **identification of the circle fold's second layer with the odd part** of the
     `x`-projection, which is the step that would let §75 transfer verbatim and give the sharp
     `1/|F|` instead of `n/|F|`.

So the honest verdict is: the *interface* is a dozen lines, the *mathematics behind it* is not,
and a definition without (1) and (2) would be decoration.  It is therefore left as future work,
and the gap recorded in §76 stands unchanged.  Nothing about the circle code is asserted as
proved in this repository.

## 79. The circle bridge: falsification first, then the zero-count theorem

The question this section settles is the one left open by §76 and §78: *what exactly connects
the structured-second-layer theorem (§74) to the circle code?*  The rule followed was
falsification before formalisation — the semantic audit is in `CIRCLE_BRIDGE_OBLIGATIONS.md`,
the experiment in `analysis/circle_bridge_falsification.py` (exact integer arithmetic, output
saved alongside).

### 79.1 What a circle word is — bridge A refuted at the level of the code

The circle code on `D ⊆ Circle F` is `C_k(D) = {a(x) + y·b(x) : deg a, deg b < k}`, the image
of the coordinate ring `F[X,Y]/(Y² − (1 − X²))`, i.e. a free rank-two `F[X]`-module — **not**
ordinary polynomial evaluation.  Test T1: 172 of 172 sampled circle words on twin-coset domains
fail to be functions of `x`; first counterexample `q = 7`, `D = {(2,2),(5,5),(2,5),(5,2)}`,
`a = 4`, `b = 6`, word `(2,6,6,2)` — two positions share `x` with different values.  So the
identification "circle second layer = one polynomial `g(x)`" is **false as stated for the
circle code**, and everything that assumed it was assuming something unproved.

Test T2 records the compatible positive fact: after the `J`-fold (`J` = inversion
`(x,y) ↦ (x,−y)`), the second layer of a circle word *is* the ordinary polynomial `b` on the
projected domain — 0 failures in 172.  But that is a **different MCA instance**: test T6
compares the strong bad set of the folded univariate instance with that of the circle instance
built from the same two layers and finds them different in 35 of 80 cases, with separating
examples in both directions (`q = 7`: `#Bad(folded) = 1` vs `#Bad(circle) = 0`, and
`#Bad(folded) = 1` vs `#Bad(circle) = 2`).  So the univariate certificate of §75 does **not**
transfer to the circle code by folding.

### 79.2 What the existing proof really uses — the zero-count theorem

Re-reading the proof of `card_badSet_le_one_of_structured_snd`, the polynomial degree window
enters at exactly two points: `f₁` is not a codeword, and a nonzero difference `f₁ − c` agrees
with `0` on fewer than `t` positions.  Nothing else.  The general theorem is therefore

> `Root.CodingTheory.Alphabet.card_badSet_le_one_of_zeroCount`
> (`RequestProject/Root/CodingTheory/ZeroCountSecondLayer.lean`):
> for an arbitrary linear code `C : Submodule F (ι → A)` over an arbitrary alphabet, if
> `f₁ ∉ C`, every codeword agrees with `f₁` on fewer than `t` positions, and `2e + t ≤ n`,
> then `#Bad ≤ 1`, hence `ε_mca ≤ 1/|F|`.

No minimum distance, no `3e < d`, no Reed–Solomon structure.  The companion
`badSet_eq_empty_of_snd_mem` gives the empty regime from `f₁ ∈ C` alone (weaker hypothesis than
the existing `badSet_eq_empty_of_mem`, which needs both layers in the code).

### 79.3 The circle instantiation

`RequestProject/Root/CodingTheory/CircleZeroCount.lean`:

* `circleNorm a b = a² − (1 − X²)b²` is nonzero for `(a,b) ≠ (0,0)` — proved by parity of the
  multiplicity of the root `1`.  **Characteristic 2 is excluded and must be**: over `F₂`,
  `1 − X² = (1 + X)²`, and the nonzero word `(1 + X) + y·1` vanishes on the whole circle
  (recorded as test T3b).
* `card_circleZeros_le`: a nonzero circle word vanishes at at most `deg (circleNorm a b)` points
  of `D`.  The count matches fibres of the `x`-projection against root multiplicities: a fibre
  with two zeros forces `a(x) = b(x) = 0`, hence a *double* root.  Test T3: 6 448 words, 0
  violations of `#zeros ≤ deg N` and of `#zeros ≤ 2t'`, with 12 instances attaining `2t'`.
* `card_badSet_circle_le_one`: if the second layer is a circle word with `deg a, deg b < t`,
  at least one of them `≥ k`, and `2e + 2t + 1 ≤ |D|`, then `#Bad ≤ 1` — whatever the first
  layer is.  Test T4: 176 instances inside the hypothesis, max `#Bad = 1` (96 attain 1);
  control without the window reaches `#Bad = 3`.
* `circle_epsMCA_le_two_pow_neg_128`: `|D| = 2²⁰`, `k = 2¹⁸` (dimension `2k = 2¹⁹`, rate
  `ρ = 1/2`), second layer with `deg a = k`, `e = 262142` (`δ ≈ 0.2499981`) ⇒ `ε_mca ≤ 2⁻¹²⁸`
  for `|F| ≥ 2¹²⁸`.

The hypotheses ask **nothing** about the shape of `D` — no twin coset, no `J`-stability, no
completeness of the `x`-fibres, and points with `y = 0` are allowed.  Test T7 confirms this
empirically: 398 instances on arbitrary circle domains (115 containing a point with `y = 0`,
199 with an incomplete `x`-fibre), max `#Bad = 1`.

### 79.4 Sharpness of the slack, and what minimum distance does not give

* The `+1` in `2e + 2t + 1 ≤ |D|` is necessary.  Fixed reproducible witness (same script):
  `q = 31`, twin coset `|D| = 8`, `k = 2`, `t' = 3`, `e = 1`, `a = 18 + 19X + 3X²`,
  `b = 24 + 18X + 5X²`, `f₀ = (3,9,0,0,8,24,10,10)` — `2e + 2t' = 8 = |D|` and the strong bad
  set is `{0, 19}`, so `#Bad = 2`.
* Minimum distance alone is **not** enough (test T5, refuting implication (ii) of the audit):
  `q = 31`, `|D| = 8`, `k = 2`, `d = 4`, `e = 1` (so `3e < d`, the unique-decoding regime), and
  an unstructured second layer gives `#Bad = 2`.  The structural hypothesis is doing real work;
  distance-only gives at best the generic `n/|F|` of `Alphabet.card_badSet_le`.

### 79.5 Status

Exactly one bridge was chosen (route **C**, zero count), proved, and instantiated; routes **A**
(ordinary-polynomial identification for the circle code) and the distance-only route are
refuted with explicit counterexamples.  No circle-code library, no Circle-STARK soundness
claim, and no multi-round statement was added.

## 80. The Circle-FRI prover-word lemma after one inversion fold, and the one-round certificate

Exact semantics: `CIRCLE_FOLD_SEMANTICS.md`.  Numerical pre-verification:
`analysis/circle_fold_prover_word_check.py` (output saved alongside).  Lean:
`RequestProject/Root/CodingTheory/CircleFRIProverWord.lean`.  Full `lake build` clean, no
`sorry`, every new declaration audited in `Main.lean` with only
`[propext, Classical.choice, Quot.sound]`.

### 80.1 What the fold produces

The fold is the inversion involution `J (x, y) = (x, −y) = p⁻¹` on `FFT.Circle F`; the projected
domain is `π D = D.image (·.x) : Finset F`; a fold section is `σ : ↥(π D) → FFT.Circle F` with
`σ u ∈ D`, `(σ u).x = u` and `(σ u).y ≠ 0` (it exists whenever `D` avoids the two fixed points
`y = 0` — `exists_circleFoldSection`).  The layers are

    foldFst w σ u = (w (σ u) + w (J (σ u))) / 2 ,
    foldSnd w σ u = (w (σ u) − w (J (σ u))) / (2 · (σ u).y) .

**Prover-word lemma (`circle_fold_snd_eq_eval_b`).**  If the prover's word is the circle word
`w (x, y) = a(x) + y·b(x)`, then `foldSnd w σ = eval b` and `foldFst w σ = eval a` on `π D`.
The second layer is `b(x)` itself — an *ordinary* univariate polynomial, **not** `y·b(x)` and
not a circle word.  Hypotheses: `2 ≠ 0` and the two section conditions.  Nothing about degrees,
nothing about `a`, nothing about the shape of `D`.

The `y ≠ 0` condition is not cosmetic: at a fixed point of `J` the quotient is `0/0` and `b` is
simply not determined by the word (test P4 of the script).

### 80.2 The one-round certificate

Because the layer is an ordinary polynomial on an ordinary domain, the post-fold instance is
univariate: the code is `reedSolomonCode F (π D) k` and the bookkeeping is the univariate
`2e + t ≤ |π D|`, *not* the circle `2e + 2t + 1 ≤ |D|` of §79.  The fold buys back the factor 2
that the circle norm costs.

* `circle_fri_one_round_badSet_eq_empty` — `deg b < k` ⇒ empty bad set;
* `circle_fri_one_round_card_badSet_le_one` — `k ≤ deg b < t` and `2e + t ≤ |π D|` ⇒ `#Bad ≤ 1`,
  whatever the first layer;
* `circle_fri_one_round_epsMCA_le_one_div` — hence `ε_mca ≤ 1/|F|`;
* `circle_fri_one_round_epsMCA_le_two_pow_neg_128` — the concrete `ρ = 1/2` row: `|π D| = 2²⁰`,
  `k = 2¹⁹`, `e = 262143` (`δ ≈ 0.2499990`), `deg b = 2¹⁹` ⇒ `ε_mca ≤ 2⁻¹²⁸` for `|F| ≥ 2¹²⁸`.

Scope: one round, one line, a prover word of the form `a(x) + y·b(x)`.  No multi-round
soundness and no Circle-STARK claim.

### 80.3 Numerical record

840/840 twin-coset instances and 4080/4080 arbitrary-domain instances confirm both layer
identities; 420/420 instances confirm that the layers do not depend on the chosen section; the
one-round bad-set scan gives `max #Bad = 1` in the window regime (270 instances) and `#Bad = 0`
in the low-degree regime (270 instances); the earlier 172/172 experiment was re-run unchanged.

## 81. Generality extraction checkpoint: one mechanism behind all the `#Bad ≤ 1` certificates

Document: `GENERALITY_CHECKPOINT.md`.  Lean:
`RequestProject/Root/CodingTheory/ZeroLocusGeneral.lean`.

### 81.1 The mechanism

For an arbitrary field `F`, finite index type `ι` and module alphabet `A`, call a code
`V : Submodule F (ι → A)` **zero-bounded with parameter `t`** if every nonzero word of `V`
vanishes at fewer than `t` positions.  Then `zeroBounded_iff_minDistGe` shows this is *exactly*
the statement that `V` has minimum distance `≥ |ι| − t + 1`, and

    f₁ ∉ C ,  C ≤ V ,  f₁ ∈ V ,  ZeroBounded V t ,  2e + t ≤ |ι|   ⟹   #Bad ≤ 1 ,  ε_mca ≤ 1/|F| .

No polynomials, no evaluation map, no geometry, no field structure on the alphabet.

### 81.2 Four instances, all through the generic theorem

| instance | ambient `V` | parameter | source of the zero bound |
|---|---|---|---|
| ordinary Reed–Solomon | `reedSolomonCode F D t` | `t` | root counting |
| circle code | `circleCode D t'` | `2t' + 1` | norm counting, needs `2 ≠ 0` |
| Circle-FRI round (post-fold) | `reedSolomonCode F (π D) t` | `t` | root counting |
| folded Reed–Solomon, block alphabet `Fin s → F` | `foldedRSCode B k' s γ` | any `t > ⌊(k'−1)/s⌋` | the folded minimum distance already proved in the project |

The fourth row is the abstraction test and required no new mathematics:
`foldedRS_card_badSet_le_one` and `foldedRS_epsMCA_le_one_div` follow from
`foldedRS_minDistGe` alone.  So a *new code needs exactly one new lemma* — a minimum-distance
bound — to inherit the whole certificate.

### 81.3 What stays specific, and one artefact removed

Specific: the derivation of the zero bound is per-code (root counting vs. norm counting), and
the prover-word lemma is per-fold (`friSnd_eval` for radix-2, `circle_fold_snd_eq_eval_b` for
the circle inversion).  The mechanism is also confined to `2e + t ≤ |ι|`, a unique-decoding
condition; no capacity claim follows from it.

Artefact removed: `badSet_eq_alphabet_badSet` and `epsMCA_eq_alphabet_epsMCA` prove that the
polynomial-existential `badSet` of `MCA.lean` and the submodule-existential `Alphabet.badSet`
of `AlphabetMCA.lean` are the *same* finite set and the same probability, so the univariate MCA
layer is literally the alphabet-generic layer specialised at the Reed–Solomon code.  This
correspondence had only been informal.

## 82. The zero-locus frontier: weakest hypothesis, a list-size theorem, and the barrier

Full detail in `ZEROBOUNDED_STATUS.md`, `ZERO_LOCUS_FRONTIER.md`,
`ZERO_BOUNDED_FAILURE_MODE.md` and `ZERO_LOCUS_EXPERIMENTS.md`.  Lean file:
`RequestProject/Root/CodingTheory/ZeroLocusListSize.lean`.  Notation: `n = |ι|`, `d = d(C)`,
`w = d(f₁, C)`, `#Bad = (Alphabet.badSet C e f₀ f₁).card`.

### 82.1 The mechanism needs only one distance inequality

`FarFrom C r f := ∀ c ∈ C, r < hammingDistance f c`.  Proved:

    card_badSet_le_one_of_farFrom :  d(f₁, C) > 2e  ⟹  #Bad ≤ 1 ,  ε_mca ≤ 1/|F|

with no side conditions (`f₁ ∉ C` and `2e < n` are consequences), and

    farFrom_iff_exists_zeroCountLt :
        d(f₁,C) > 2e  ↔  f₁ ∉ C ∧ ∃ t, ZeroCountLt C t f₁ ∧ 2e + t ≤ n .

So the zero-count package of §80–§81 *is* the single inequality `d(f₁,C) > 2e`; the mechanism
is a repackaging of the unique-decoding argument, and `ZeroBounded` is (as §81 already showed)
minimum distance.  `FarFrom` is strictly weaker than the ambient-code hypothesis: over `F₅`
with `C = span{(1,1,0,0,0)}`, `f₁ = (1,1,1,1,1)`, `e = 1`, the `FarFrom` theorem applies
(`Separation.card_badSet_le_one_sep`) while *no* ambient zero-bounded code exists
(`Separation.no_zeroBounded_ambient`).

### 82.2 A list-size theorem with `L > 1`

    card_badSet_le_hammingDistance :
        MinDistGe C d ,  q ∈ C ,  2e + 2·d(f₁,q) < d   ⟹   #Bad ≤ d(f₁,q)

— equivalently `#Bad ≤ n − |Z|` where `Z` is the zero locus of `f₁ − q`
(`card_badSet_le_card_compl_zeroLocus`).  This covers the regime the previous theorem cannot
see (second layer *close* to the code) and is attained at `L = 2`: RS `[10,4]` over `F₁₁`,
`e = 1`, `w = 2`, `#Bad = 2` (`analysis/zero_locus_list_size_targeted.py`, T1).  Its hypothesis
is necessary: RS `[4,2]/F₅`, `e = 1`, `w = 2` gives `#Bad = 4`.

Auxiliary result of independent use: `badSet_sub_codeword` — the bad set depends on the second
layer only through its coset modulo `C`, i.e. only through its syndrome.

Combining the two regimes with no hypothesis on the second layer:

    card_badSet_le_two_mul_of_six_mul_lt_minDist :  6e < d  ⟹  #Bad ≤ max 1 (2e) ,

against the previous alphabet-generic row `#Bad ≤ n` under `3e < d`.

### 82.3 The barrier, and the circle factor 2

The two regimes leave the gap `(d − 2e)/2 ≤ w ≤ 2e` (nonempty iff `d ≤ 6e`), and inside it
`#Bad` reaches `|F| − 1` in explicit instances, so no bound in `(e, w, d, n)` can hold there.
Crossing it requires controlling the list of codewords near `f₁`, not the zero locus of one
difference.  All regimes remain inside unique decoding; no Johnson or capacity claim is made.

`finrank_le_of_zeroBounded` (Singleton: a zero-bounded code has dimension `≤ t`) plus an
exhaustive circle scan settle the factor-2 question: the circle bound `#zeros ≤ 2t'` is
*attained* on the circles of `F₇, F₁₁, F₁₃` at `t' = 2`, and no code of dimension `2t'` admits
a zero bound below `2t' − 1`.  The factor 2 is the dimension of the circle code (two
polynomial layers), not an artefact of the norm argument; no separate parameter `κ` is
introduced.

## 83. Geometric charging: the bad set consumes the resources of the nearby-codeword list

All statements of this section are Lean theorems in
`RequestProject/Root/CodingTheory/ListGeometrySlopeBound.lean` (`lake build`, no `sorry`,
axioms exactly `propext, Classical.choice, Quot.sound`; the file ends with its own
`#print axioms` audit).  Notation as in §82: `C ≤ (ι → A)` a linear code over a field `F` with
an `F`-module alphabet, `n = |ι|`, radius `e`, line `γ ↦ f₀ + γ f₁`, `w = d(f₁,C)`,
`L(f₁,2e) = {q ∈ C : d(f₁,q) ≤ 2e}`.

### 83.1 The charging lemma

`Alphabet.exists_charging`: if `1 < #Bad`, there is a map `chg : F → (ι → A) × ι` with, for
every bad `γ`,

* `(chg γ).1 ∈ C` and `d(f₁, (chg γ).1) ≤ 2e` — the charged codeword lies in `L(f₁,2e)`;
* `f₁ ((chg γ).2) ≠ (chg γ).1 ((chg γ).2)` — the charged position lies in `supp(f₁ − q)`;
* `chg` is injective on the bad set.

So the bad set injects into the disjoint union `⨆_{q ∈ L(f₁,2e)} supp(f₁ − q)` of resource
packets of sizes `d(f₁,q)`.  Four ingredients, each a lemma of the same file: the secant slope
of two bad witnesses is a codeword within `2e` of `f₁` (`hammingDistance_slope_le`,
`slope_mem`); the witness codewords of one slope class are affine in `γ` with a common
intercept; badness forces a disagreement position with the slope on the agreement set
(`exists_pin`); and there the scalar equation determines `γ`.  **No minimum-distance
hypothesis, no Reed–Solomon structure and no decoding-radius hypothesis is used.**

### 83.2 Counting corollaries

| statement | Lean name |
| --- | --- |
| `Q ⊇ L(f₁,2e) ⇒ #Bad ≤ max 1 (∑_{q∈Q} d(f₁,q))` | `card_badSet_le_sum_hammingDistance` |
| `#Bad ≤ max 1 (2e·|Q|)` | `card_badSet_le_two_mul_mul_card` |
| list forms of both | `card_badSet_le_sum_nearbyList`, `card_badSet_le_two_mul_mul_card_nearbyList` |
| `L(f₁,2e) = ∅ ⇒ #Bad ≤ 1` (§82 far regime) | `card_badSet_le_one_of_empty_list` |
| unique nearby `q ⇒ #Bad ≤ max 1 (d(f₁,q))`, **without** `2e+2w<d` | `card_badSet_le_hammingDistance_of_unique_nearby` |

The last row is the gain over §82: the close-regime bound now holds inside the gap
`(d−2e)/2 ≤ w ≤ 2e`.  The conjecture recorded as D82.2 (`#Bad ≤ max(1, L·2e)`) is hereby
**proved**; see D82.2 in `DISCREPANCIES.md`.

### 83.3 Experiments and falsified alternatives

`analysis/geometric_charging_probe.py` (+ `…_progress.json`, `…_output.txt`),
`analysis/geometric_charging_extra_checks.py`, `analysis/list_geometry_probe.py`; exact integer
arithmetic, instances enumerated over coset representatives inside the gap.  Over 39 530 gap
instances with `#Bad ≥ 2` the charging is confirmed in every case (witness in the list, position
found, injective, load of each slope `≤ d(f₁,q)`; maximal observed load 3).  Falsified
alternatives, with minimal counterexamples: `#Bad ≤ ∑ d(f₁,q)` without the floor 1
(`RS[4,1]/F₅`, empty list, `#Bad = 1`), `#Bad ≤ max(1,w)` (`RS[4,2]/F₅`, `#Bad = 3`),
`#Bad ≤ max(1, max_q d(f₁,q))` (same instance), and the boundary/branching invariant
`#Bad ≤ |⋃_q supp(f₁−q)|` (`RS[6,3]/F₇`, `e = 2`: boundary mass 6, `#Bad = 7` — which also
refutes `#Bad ≤ n`).  The minimum-spanning-tree mass of `{f₁} ∪ L` was never smaller than the
radial sum in 582 gap configurations, so tree geometry adds nothing here.  Full report:
`GEOMETRIC_CHARGING_AUDIT.md`; the earlier invariant screening is in `LIST_GEOMETRY_PROBE.md`.

No bound on `|L(f₁,2e)|` is proved, so no Johnson, capacity or performance claim follows.

## 84. Capacity refinement: a nearby codeword can absorb at most `e+1` bad parameters

All statements are Lean theorems in `RequestProject/Root/CodingTheory/ChargingCapacity.lean`
(`lake build` clean, no `sorry`, axioms exactly `propext, Classical.choice, Quot.sound`; the file
ends with its own `#print axioms` audit).  Notation as in §83.

### 84.1 The packing (load) lemma

Inside one slope class the witness codewords are affine, `c_γ = h + γ·q`, and the witness
agreement set has at least `n − e` positions.  Hence a bad `γ` of the class solves
`f₀ + γ f₁ = h + γ q` at at least `d(f₁,q) − e` of the `d(f₁,q)` positions where `f₁ ≠ q`, and
two distinct parameters of the class never solve it at the same position.  A slope class is
therefore a disjoint packing of nonempty sets of size `≥ max(1, d(f₁,q) − e)` inside a set of
size `d(f₁,q)` (`Alphabet.card_le_chargeCap`, stated abstractly — no code, no badness):

    |class(q)| ≤ chargeCap e (d(f₁,q)),
    chargeCap e m = m for m ≤ e,  min(m, ⌊m/(m−e)⌋) for m > e,
    chargeCap e m ≤ e + 1 always,  ≤ 2 as soon as 3e < 2m.

### 84.2 Counting corollaries

| statement | Lean name |
| --- | --- |
| `Q ⊇ L(f₁,2e) ⇒ #Bad ≤ max 1 (∑_{q∈Q} chargeCap e (d(f₁,q)))` | `card_badSet_le_sum_chargeCap` |
| `Q ⊇ L(f₁,2e) ⇒ #Bad ≤ max 1 ((e+1)·|Q|)` | `card_badSet_le_succ_mul_card` |
| all `q ∈ Q` at distance `> 3e/2` ⇒ `#Bad ≤ max 1 (2·|Q|)` | `card_badSet_le_two_mul_card_of_two_mul_le` |
| explicit-list forms | `card_badSet_le_sum_chargeCap_nearbyList`, `card_badSet_le_succ_mul_card_nearbyList` |
| Reed–Solomon realisations | `rs_card_badSet_le_sum_chargeCap`, `rs_card_badSet_le_succ_mul_card` |

Gain over §83: the per-codeword factor `2e` becomes `e + 1` (and `2` in the extremal regime
`d(f₁,q) > 3e/2`), the weight form is strictly sharper since `chargeCap e m ≤ m`, and the
list-size form no longer needs the hypothesis that the elements of `Q` are close to `f₁`.

### 84.3 Experiments and the remaining obstacle

`analysis/list_geometry_frontier.py`: 34 514 gap instances over eleven Reed–Solomon families
(F₅, F₇, F₁₁, F₁₃), exact integer arithmetic; the load bound and both new corollaries hold
without exception, and the aggregate sharpening `∑ d(f₁,q) − ∑ chargeCap e (d(f₁,q))` is 414 796.
`analysis/achieved_slopes_probe.py`: over 2 033 gap instances with `#Bad ≥ 2` the step
`#Bad ≤ ∑_{achieved slopes} chargeCap` is tight (ratio 1.0), while the passage from achieved
slopes to the full list loses everything — largest achieved-slope count 9 against list size 136.
The achieved-slope count `A` has no cheap bound: `A ≤ e+1`, `A ≤ 2e`, `A ≤ w+1` and `A ≤ n` all
have explicit counterexamples (e.g. RS[6,3]/F₁₁, `e = 2`, `n = 6`, `A = 9`, `#Bad = 10`).  So the
residual obstacle is exactly a list-decoding-type bound on `A`.  Full report:
`LIST_GEOMETRY_FRONTIER.md`.

Still no bound on `|L(f₁,2e)|` or on `A` is proved, hence no Johnson, capacity or performance
claim follows.

## 85. The global ambiguity gate: a scalable barrier (`Root/CodingTheory/AmbiguitySaturation.lean`)

The window-free decomposition `#Bad ≤ (ℓ−1)(e+1) + |A|` of §84's companion file
(`AmbiguityBarrier.lean`) leaves one quantity open: the number `|A|` of *ambiguous* challenges.
This section closes it negatively.

| statement | name |
|---|---|
| canonical ambiguous set (smallest admissible `A`) | `PolyGen.ambiguousSet`, `mem_ambiguousSet`, `ambiguousSet_split`, `ambiguousSet_subset_of_split` |
| sandwich `#Bad − (ℓ−1)(e+1) ≤ |A| ≤ #Bad` | `card_sub_sharp_le_card_of_split`, `card_ambiguousSet_le_card_badSetG` |
| saturating family (`D = F`, `ℓ = 2`, `k = |F|−2`, `e = 1`): every nonzero challenge is bad | `Saturation.isBadG_satFam`, `Saturation.card_badSetG_satFam_ge` |
| its parameters miss the window by one position | `Saturation.satFam_outside_window` |
| hence `\|A\| ≥ |F| − 3` for every candidate codeword family and every admissible `A` | `Saturation.card_ambiguous_satFam_ge`, `Saturation.card_ambiguousSet_satFam_ge` |
| prime-field form `\|A\| ≥ p − 3` | `Saturation.card_ambiguousSet_satFam_zmod_ge` |

So one position outside the sharp window the ambiguous set is all but three challenges, for every
finite field with `|F| ≥ 4`: the ambiguity decomposition cannot by itself enlarge the regime.
Exact independent check for `p = 5, 7, 11, 13`: `analysis/ambiguity_saturation_check.py`.
Full report: `docs/AMBIGUITY_SATURATION_REPORT.md`.

## 86. Sparse domains: the arity-`ℓ` circuit-incidence bound and its sharpness (`Root/CodingTheory/GeneratorCircuitIncidence.lean`, `Root/CodingTheory/SparseDomainSharpness.lean`)

§85 showed that one position outside the sharp window the bad set can be *all* of the challenge
space — but only on the full domain `D = F`.  This section isolates the domain as the responsible
parameter and removes the window from the generator bounds.

| statement | name |
|---|---|
| Lagrange coefficients at `ℓ` nodes | `PolyGen.exists_lagrange_coeffs` |
| challenge capacity: `ℓ` accepted challenges on one set trap the whole family | `PolyGen.genCloseOn_of_forall_isCloseOn` |
| circuit incidence at arity `ℓ`: `#Bad·C(T−1,a−1) ≤ C(\|D\|,a)·(ℓ−1)`, `T = max(\|D\|−e, k+1)` | `PolyGen.card_badSetG_le_circuit` |
| window-free, field-free: `#Bad ≤ (ℓ−1)·C(\|D\|,k+1)` | `PolyGen.card_badSetG_le_choose` |
| sparse form `#Bad ≤ (ℓ−1)·C(\|D\|,e)` (for `k+1 ≤ \|D\|−e`) | `PolyGen.card_badSetG_le_choose_sparse` |
| at `e = 1`: `#Bad ≤ (ℓ−1)·\|D\|` for every `k ≤ \|D\|−2` | `PolyGen.card_badSetG_le_of_e_le_one` |
| no saturation on a sparse domain; `ε_mca ≤ (ℓ−1)C(\|D\|,e)/\|F\|` | `PolyGen.card_badSetG_lt_of_sparse`, `PolyGen.epsMCAG_le_choose_sparse` |
| the extremal family `f₀ x = x^{\|D\|−e−1}`, `f₁ x = x^{\|D\|−e}` and its local interpolants | `PolyGen.SparseSharp.famSparse`, `vanishOnSet`, `interpSparse` |
| every `(\|D\|−e)`-subset with nonzero sum yields a bad challenge `−(∑A)⁻¹` | `PolyGen.SparseSharp.isBadG_famSparse` |
| **tightness at every budget**: `#Bad = C(\|D\|, e)` exactly, at `ℓ = 2`, `k = \|D\|−e−1` | `PolyGen.SparseSharp.card_badSetG_famSparse_eq` (lower bound `card_badSetG_famSparse_ge`) |
| those parameters are outside the window for every `e ≥ 1` | `PolyGen.SparseSharp.famSparse_outside_window` |
| at `e = 1`: `#Bad = \|D\|` exactly, under `∑D ∉ D` | `PolyGen.SparseSharp.card_badSetG_famSparse_eq_of_e_one` |
| concrete: `ZMod 11`, `D = {1,2,3}`, `#Bad = 3` of `11` | `PolyGen.SparseSharp.card_badSetG_sparse_zmod11` |
| consistency with §85: at `D = F` the bound gives `\|F\|`, the family gives `\|F\|−1` | `PolyGen.SparseSharp.card_badSetG_satFam_sandwich` |

None of these bounds mentions `|F|`: the number of bad challenges outside the window is governed
by the *domain*, and the §85 saturation is a phenomenon of `|D| = |F|` only.  At `ℓ = 2` the
circuit bound coincides with the known line bound of the circuit-incidence file (`card_badSet_le_circuit`); the new
content is arity `ℓ ≥ 3`, where no window-free bound existed, and the exact value `C(|D|, e)` at
`ℓ = 2`, which shows the sparse bound cannot be improved by any better incidence argument.
Reconnaissance: `analysis/sparse_domain_saturation_probe.py` (at `e = 1`, max `#Bad` found is
exactly `(ℓ−1)|D|`, independent of `|F|`),
`analysis/sparse_domain_general_e_probe.py` (at `ℓ = 2`, `e ∈ {2,3}` the maximum stops at
`C(|D|, e)` and does not grow with `|F|`), `analysis/circuit_ceiling_scan.py` (numerical ceiling
of the circuit bound).  Full report: `docs/SPARSE_DOMAIN_CIRCUIT_REPORT.md`.

## 87. Syndrome-complexity phase theory: the support-concentration law, the rigidity dichotomy and a linear window (`Root/CodingTheory/SyndromeSupportPhase.lean`, `SupportPhaseSharpness.lean`, `SyndromeRigidityDichotomy.lean`, `RigidityMCAConsequence.lean`, `SyndromeWindowReduction.lean`)

The Hankel route of the previous section carried a non-degeneracy hypothesis (`det H_e ≠ 0`).
This section removes it, replaces it by an explicit dichotomy on the *joint syndrome support*, and
shows both branches are attained exactly.

| statement | name |
|---|---|
| support-concentration law `#Bad·(t−e) ≤ t(ℓ−1)`, `t` = joint syndrome support | `PolyGen.Hankel.card_mul_sub_le_core`, `exists_support_card_mul_sub_le` |
| converse syndrome dictionary (moments = power sums ⇒ closeness) | `PolyGen.Hankel.isCloseOn_of_mom_eq_power_sum`, `exists_syndromeSupport` |
| large support ⇒ small bad set (`t ≥ e+1 ⇒ #Bad ≤ (e+1)(ℓ−1)`) | `PolyGen.Hankel.card_le_of_support_ge` |
| large bad set ⇒ concentrated support (`#Bad ≥ 2(ℓ−1) ⇒ t ≤ 2e`; `≥ (e+1)(ℓ−1) ⇒ t ≤ e+1`) | `support_le_two_mul_of_card_ge`, `support_le_succ_of_card_ge`, `card_lt_two_mul_of_support_gt` |
| the dichotomy | `PolyGen.Hankel.card_le_or_support_le` |
| trap lemma inverse: `ℓ` accepted challenges force each generator close | `PolyGen.isCloseOn_basis_of_forall_isCloseOn` |
| the rigid class `RigidOn ℓ k e f` (all `f_j` close to the code off one `≤ e`-set) | `PolyGen.RigidOn` |
| rigid bound `#Bad ≤ e(ℓ−1)` in the window `k+2e ≤ \|D\|` | `PolyGen.card_badSetG_le_of_rigid` |
| rigidity dichotomy `#Bad ≤ (e+1)(ℓ−1) ∨ RigidOn ℓ k e f` | `PolyGen.card_le_or_rigid` |
| **unconditional bound** `#Bad ≤ (e+1)(ℓ−1)` (window `e((e+1)(ℓ−1)+1)+k ≤ \|D\|`, no genericity) | `PolyGen.card_badSetG_le_unconditional` |
| generic-phase sharpness: plane family has `#Bad = \|T\|(ℓ−1)`, hence `(e+1)(ℓ−1)` | `PolyGen.card_badSetG_famPlane_card_mul`, `card_badSetG_famPlane_eq` |
| rigid-phase sharpness: the plane family on `e` locators is rigid with `#Bad = e(ℓ−1)` | `PolyGen.rigidOn_famPlane`, `card_badSetG_famPlane_rigid_eq`, `exists_rigid_pencil_card_badSetG_eq` |
| MCA consequence at arity 2: `#Bad ≤ e+1`, `ε_mca ≤ (e+1)/\|F\|` | `PolyGen.card_badSet_le_rigidity`, `epsMCA_le_rigidity` |
| strict gain over the previous line bound `(k+1)e+1` | `PolyGen.lt_card_badSet_le_unconditional_bound` |
| bootstrapping: any subfamily of `≥ 2ℓ−2` bad challenges has joint support `≤ 2e` | `PolyGen.biUnion_card_le_two_mul` |
| **linear window**: `(2ℓ−2)e+k ≤ \|D\|` and `3e+k ≤ \|D\|` ⇒ `#Bad ≤ (e+1)(ℓ−1)` | `PolyGen.card_badSetG_le_linear_window` |
| line form (`3e+k ≤ \|D\|` ⇒ `#Bad ≤ e+1`) and its `ε_mca` form | `PolyGen.card_badSet_le_linear_window`, `epsMCA_le_linear_window` |

So the phase law is exact rather than merely an upper bound: joint support `≤ e` (rigid phase) gives
maximum `e(ℓ−1)`, joint support `≥ e+1` (generic phase) gives maximum `(e+1)(ℓ−1)`, and both maxima
are realised by explicit families for every `e`, `ℓ`.

Two conjectures of the directive are refuted by these families.  The Grassmannian heuristic
`#Bad ≤ 4 − 2/e` (i.e. `#Bad ≤ 3` for `e ≥ 3` at `ℓ = 2`) is false: the plane family gives
`#Bad = e+1` for every `e`.  The strong redundancy/gcd law is false as well: the sharp family
survives maximal redundancy, and `natDegree_gcd_shiftDet_famPlane_ge` shows the gcd of any two
offset determinants still has degree `≥ (e+1)(ℓ−1)`.  The narrow window is necessary: the
project's certified `four_le_card_badSetG_gapWitness` (`ZMod 5`, `|D| = 4`, `k = 2`, `e = 1`) has
`#Bad = 4 > e+1` exactly at `k+2e = |D|`.

Reconnaissance (not proof): `analysis/syndrome_support_phase_probe.py`,
`analysis/rigid_phase_probe.py` — zero violations, every bound attained.  Full report:
`docs/SYNDROME_SUPPORT_PHASE_REPORT.md`.

## 88. Cyclotomic cosets compute the exact bilinear complexity of cyclic convolution over M31 (`FrobeniusOrbits.lean`, `CyclotomicFactorCount.lean`)

`ConvExact.lean` reduced the exact bilinear complexity of length-`n` cyclic convolution over a
field `F` with `char F ∤ n` to `2n − t(n)`, where `t(n)` is the number of maximal ideals of the
group algebra `F[C_n]` (equivalently the number of monic irreducible factors of `xⁿ − 1` over `F`).
Up to now `t(n)` was only accessible over `M31` through the divisor-sum formula of
`FactorCount.lean` (`tM31`, valid for `n ≤ 60` where a table of multiplicative orders was
certified).  The classical description — the factors are in bijection with the *q-cyclotomic
cosets* of `ℤ/n`, i.e. the orbits of multiplication by `q = |F|` — was flagged as an open gap in
`factorCount_le_cover`.  It is now proved.

`FrobeniusOrbits.lean` develops the orbit combinatorics:

| statement | name |
| --- | --- |
| Galois descent: `x^{|K|} = x → x ∈ range (algebraMap K L)` for finite fields | `FFT.mem_range_algebraMap_of_pow_card_eq` |
| the coset `{q^k · j : k}` of `j ∈ ℤ/n` as a `Finset` | `FFT.frobClass` |
| membership is an equivalence: `i ∈ frobClass q j ↔ frobClass q i = frobClass q j` | `FFT.mem_frobClass_iff_eq` |
| the computable orbit count `t(n)` | `FFT.frobClassCount` |
| `q ≡ −1 (mod m)`, `2 ≤ m` ⇒ the count is `m/2 + 1` | `FFT.frobClassCount_of_neg_one` |

`CyclotomicFactorCount.lean` identifies the maximal ideals.  For a primitive `n`-th root of unity
`ζ` in an extension `K/F`, evaluation at `ζ^j` gives an `F`-algebra map `F[C_n] → K`; its kernel
`evalKer` is maximal, and the key theorem

* `FFT.Bilinear.evalKer_eq_iff` — `evalKer j = evalKer i ↔ i ∈ frobClass q j`

(one direction by Frobenius invariance, the other by descending the coset polynomial
`∏_{i ∈ frobClass q j}(X − ζ^i)` to `F[X]` via the Galois-descent lemma).  Together with
`exists_evalKer_eq` (every maximal ideal is such a kernel) this gives

* `FFT.Bilinear.factorCount_eq_frobClassCount` — `t(n) = #{q-cyclotomic cosets of ℤ/n}`,
* `FFT.Bilinear.factorCount_M31_eq_frobClassCount` and
  `FFT.Bilinear.convComplexity_M31_frobClassCount` — over `M31`, for every `n` with
  `mersenne31 ∤ n` and `2n ≤ mersenne31`, the exact bilinear complexity of length-`n` cyclic
  convolution is `2n − frobClassCount mersenne31 n`, a kernel-computable number with **no**
  table of orders and **no** bound `n ≤ 60`.

Consequences.  New exact values beyond the old range, obtained by `decide +kernel`:

| `n` | `t(n)` | exact complexity `2n − t(n)` |
| --- | --- | --- |
| 100 | 11 | 189 (`cyclicConv100_M31_bilinear_complexity`) |
| 127 | 2 | 252 (`cyclicConv127_M31_bilinear_complexity`) |

and a closed form for the radix-2 lengths, the ones actually used by FFT implementations.  Since
`2^31 ≡ 1 (mod 2^31−1)`, one has `q ≡ −1 (mod 2^k)` for `1 ≤ k ≤ 31`, so
`FFT.Bilinear.frobClassCount_M31_two_pow` gives `t(2^k) = 2^{k−1} + 1` and hence

* `FFT.Bilinear.cyclicConv_M31_two_pow_bilinear_complexity` — for `1 ≤ k ≤ 29` the exact bilinear
  complexity of length-`2^k` cyclic convolution over `M31` is exactly `3·2^{k−1} − 1`,
* `FFT.Bilinear.cyclicConv_M31_two_pow_twenty` — in particular `n = 2²⁰` costs exactly
  `1 572 863` general multiplications, neither more nor less.

This is the first *closed-form, both-directions* complexity statement of the project for the
lengths of practical interest: the upper bound is a construction and the lower bound is a
Winograd-type obstruction, so `3·2^{k−1} − 1` is optimal over `M31`, not merely achievable.
Finally `FFT.Bilinear.frobClassCount_eq_tM31` cross-checks the two independent computations of
`t(n)` (orbit count vs. divisor sum) for every `n ≤ 60`, and
`factorCount_M31_thirty_via_cosets` re-derives `t(30) = 12`, previously obtained from the explicit
48-product length-30 algorithm.  The gap noted at `factorCount_le_cover` is thereby closed.

## 89. Redundancy is provably vacuous: the gcd hierarchy counts exactly the low-complexity challenges (`Root/CodingTheory/RedundancyInvariance.lean`, `SyndromeComplexityClass.lean`)

`HankelPhase.lean` built the *redundancy hierarchy*: with several available syndrome offsets
`i ∈ I` (each with `i + 2e + k + 1 ≤ |D|`) every bad challenge is a common root of the offset
determinants `D_i = shiftDet ℓ e i f`, so `#Bad ≤ deg gcd(D_i : i ∈ I)`.  The open question was
whether *more offsets provably shrink that gcd* — whether a certified bound decreasing in the
redundancy `|D| − k − 2e` can exist.  It cannot.

**The obstruction.**  The bad challenges are distinct common roots, so the *bad-set polynomial*
`badPoly = ∏_{γ ∈ Bad}(X − γ)` divides **every** available offset determinant
(`badPoly_dvd_shiftDet`), hence divides any gcd of any family of them (`badPoly_dvd_of_isGcd`).
Writing `IsGcdOf ℓ e f I G` for the universal property of a gcd (so the statement applies to
`EuclideanDomain.gcd`, to any `GCDMonoid` gcd and to any hand-built common divisor):

| statement | name |
| --- | --- |
| `badPoly ∣ D_i` for every available offset | `badPoly_dvd_shiftDet` |
| `#Bad ≤ deg G` for every gcd `G` over every offset family | `card_badSetG_le_natDegree_of_isGcd` |
| more offsets ⟹ the gcd divides the previous one | `isGcdOf_dvd_of_subset` |
| the chain is trapped: `badPoly ∣ G_J ∣ G_I` for `I ⊆ J` | `badPoly_dvd_and_dvd_of_subset` |

So the hierarchy is a divisibility chain that is weakly decreasing but **bounded below by the
truth**: the gcd bound can never beat `#Bad`, and it improves only by discarding *spurious* roots
carried by the individual determinants.

**The kill.**  On the sharp plane family of `SupportPhaseSharpness.lean` there is no spurious
content at all: `#Bad = (e+1)(ℓ−1)` equals the universal upper bound `deg D_i ≤ (e+1)(ℓ−1)`.
Hence every determinant is a constant multiple of `badPoly`
(`shiftDet_famPlane_eq_smul_badPoly`), every gcd over every nonempty family of available offsets
has degree exactly `(e+1)(ℓ−1)` (`natDegree_isGcd_shiftDet_famPlane_eq`), and two arbitrary
offset families give gcds of the same degree (`natDegree_isGcd_shiftDet_famPlane_indep`).  The
two-offset statement `natDegree_gcd_shiftDet_famPlane_ge` is thereby upgraded from `≥` to an
exact equality (`natDegree_gcd_shiftDet_famPlane_eq`), and *no* law of the form "one more offset
⟹ strictly smaller gcd", and no bound `Φ(e, ℓ, redundancy)` strictly decreasing in the
redundancy, can hold.

**What the certificate actually measures.**  `SyndromeComplexityClass.lean` identifies the root
set of the certifying determinant intrinsically.  For a challenge `γ`, put

  `SynRecur ℓ e i₀ f γ` : ∃ `v ≠ 0` with `∑_s v_s · A_{i₀+r+s}(u_γ) = 0` for all `r ≤ e`,

i.e. the syndrome window of `u_γ` obeys a nontrivial recurrence of order `≤ e` — linear
complexity `≤ e`.  Then

* `synRecur_iff_isRoot_shiftDet` — `D_{i₀}(γ) = 0 ⟺ SynRecur ℓ e i₀ f γ` (via singularity of the
  evaluated Hankel matrix);
* `badSetG_subset_synLowComplexity` — badness implies low syndrome complexity;
* `card_badSetG_add_card_falseAlarm_le` — `#Bad + #(LowComplexity ∖ Bad) ≤ deg D_{i₀}`: the slack
  of the certified bound is exactly the *false alarms*, the low-complexity challenges that are
  not bad;
* `card_badSetG_le_card_inter_synLowComplexity` — extra offsets intersect the exceptional
  classes, so they can only remove false alarms, never bad challenges;
* `synLowComplexity_famPlane_eq_badSetG` — on the sharp family the exceptional class **is** the
  bad set: zero false alarms, which is the structural reason the machinery cannot be improved
  there.

Together: the answer to "does one more syndrome offset force a universal reduction of
`deg gcd(H⁰, H¹)`?" is **no**, with an explicit scalable family on which the gcd degree is
constant in the number of offsets, and with the exact accounting of what the gcd bound measures.

## 90. The false alarms of the Hankel certificate are exactly the rigid ones (`Root/CodingTheory/SyndromeFalseAlarm.lean`)

§89 showed that the roots of the certifying determinant are the challenges of low syndrome
complexity, and that the certificate's slack is the false-alarm set `LowComplexity ∖ Bad`.  This
section determines the structure of that set.

Call `γ` **error-type** if its generated word really agrees with a codeword off a set of at most
`e` positions (`ErrorType`), and call the family **rigid on a small complement** if the family
*itself* is close off such a set (`RigidOffSmall`).  Then:

| statement | name |
| --- | --- |
| every bad challenge is error-type | `errorType_of_isBadG` |
| every error-type challenge is Hankel-singular (low complexity) | `synRecur_of_errorType` |
| the certificate chain `Bad ⊆ ErrorType ⊆ LowComplexity` | `badSetG_subset_errorTypeSet`, `errorTypeSet_subset_synLowComplexity` |
| an error-type challenge that is not bad forces the family to be close off its own error set | `genCloseOn_of_errorType_of_not_isBadG` |
| **generic phase: `ErrorType = Bad`** | `isBadG_of_errorType_of_not_rigid`, `errorTypeSet_eq_badSetG_of_not_rigid` |
| in the generic phase the slack is purely spurious | `card_badSetG_add_card_spurious_le` |

So outside the rigid branch there are **no error-type false alarms**: "the generated word has at
most `e` errors" and "the challenge is bad" are the *same* condition, and the first link of the
certificate chain carries no slack at all.  The rigid branch is not a gap either — it is exactly
the phase where `SyndromeRigidityDichotomy.lean` proves the strictly better bound `#Bad ≤ e(ℓ−1)`.

What remains between `#Bad` and `deg D_{i₀}` is therefore only the *spurious* class: challenges
whose syndrome window is Hankel-singular without any genuine `e`-error explanation.  Deciding
whether that class can be nonempty inside the available window is the converse of the key
equation and is left open (see `DISCREPANCIES.md`, D90.1) — it is not assumed anywhere.

## 91. The offset-gcd hierarchy has a redundancy-invariant floor, and the bound it yields can be corrected (`Root/CodingTheory/HankelRedundancyBarrier.lean`)

Mission question: do more available syndrome offsets force a universal reduction of
`deg gcd(D_0, …, D_r)`?  **No.**  Every entry of every offset Hankel matrix is one of the same
challenge moment polynomials `M_r`, so a common factor `P` of the `M_r` contributes `P^{e+1}` to
*every* offset determinant (`pow_dvd_shiftDet_of_dvd_momPoly`).  Intrinsically the roots of such a
factor form the *syndrome-zero locus* `Z` — the challenges whose generated word has vanishing
syndrome — and, with no hypothesis, `(∏_{γ∈Z}(X−γ))^{e+1}` divides every offset determinant
(`prod_synZero_pow_dvd_shiftDet`); hence any gcd over any offset set has degree `≥ (e+1)|Z|`
(`le_natDegree_of_isGcd_shiftDet`).

The floor is attained *at the maximum* by the collinear families `f_j = λ_j·g`: every offset
determinant is a scalar multiple of `L^{e+1}`, `L = ∑_j λ_j X^j` (`shiftDet_famScaled`), so
`deg gcd(D_{i₀},D_{i₁}) = (e+1)(ℓ−1)` for every pair of offsets
(`natDegree_gcd_shiftDet_famScaled`) while `Bad = roots(L)` has at most `ℓ−1` elements
(`badSetG_famScaled_eq`, `card_badSetG_famScaled_le`).  This is a second, mechanically different
barrier to §88: there the gcd is flat because the bound is tight, here because the determinant
carries `(e+1)`-fold wasted degree.

What survives is a strictly stronger theorem: since `Z`-elements are roots of multiplicity `≥ e+1`
and bad challenges of multiplicity `≥ 1`,

    #Bad + e·|Z| ≤ deg D_{i₀} ≤ (e+1)(ℓ−1)   and   #Bad + e·|Z| ≤ deg gcd(D_{i₀},D_{i₁}),

(`card_badSetG_add_mul_card_synZero_le_shiftDet`, `card_badSetG_add_mul_card_synZero_le`,
`card_badSetG_add_mul_card_synZero_le_gcd`), improving §87/§88 on every syndrome-degenerate family
and sharp on the barrier family (`card_badSetG_add_mul_card_synZero_famScaled_eq`).  Conversely a
family with the maximal bad set `#Bad = (e+1)(ℓ−1)` must have `Z = ∅`
(`synZeroSet_eq_empty_of_card_badSetG_eq`).  Report: `docs/HANKEL_REDUNDANCY_BARRIER_REPORT.md`;
reconnaissance: `analysis/hankel_redundancy_barrier_probe.py`.

## 92. Extremizers of the Hankel bound: a graded budget law, an equality classification, and a new proximity gain (`Root/CodingTheory/HankelExtremal.lean`, `Root/CodingTheory/HankelExtremalGates.lean`)

§91 proved `#Bad + e·|Z| ≤ (e+1)(ℓ−1)` and closed the universal-improvement routes.  This section
answers the next question: **what is forced by equality?**

The mechanism is a *unimodular column operation*.  For a witness set `T`, `|T| = m ≤ e`, the
shifted annihilators `X^{t−m}·∏_{y∈T}(X−y)`, `m ≤ t ≤ e`, assemble into an upper-triangular matrix
with unit diagonal (`annCol`, `det_annCol = 1`), so `D_{i₀} = det(hankelShift · annCol)`
(`shiftDet_eq_det_mul_annCol`).  The annihilator kills the syndrome of the witnessed word
(`annPoly_annihilates`), and this single computation yields two things at once: a challenge
witnessed by `m` errors is a root of multiplicity `≥ e − m + 1`
(`pow_X_sub_C_dvd_shiftDet_of_close`, `pow_X_sub_C_dvd_shiftDet_of_badG`); and if the *top* word is
the witnessed one, every transformed column loses its leading coefficient
(`natDegree_shiftDet_add_le_of_close_top`).

Summing multiplicities gives the **graded budget law** (`budget_law_explicit`, `budget_law_le`),
with `ρ(γ) = witnessRadius γ` the least witness size:

    ∑_{γ∈Bad∖Z} (e − ρ(γ)) + #(Bad ∪ Z) + e·|Z| ≤ deg D_{i₀} ≤ (e+1)(ℓ−1).

Error-weight slack, non-bad syndrome-zero challenges and syndrome degeneracy are charged on the
same scale.  Uniformly (`card_badSetG_mul_le_of_uniform_witness`): bad challenges all witnessed
with `≤ e−c` errors give `(c+1)·#Bad ≤ (e+1)(ℓ−1)`.

**Equality classification.**  If `#Bad + e·|Z| = (e+1)(ℓ−1)` then `Z ⊆ Bad`
(`synZeroSet_subset_badSetG_of_extremal`), every bad challenge outside `Z` has `ρ(γ) = e`
(`witnessRadius_eq_of_extremal`), `deg D_{i₀} = (e+1)(ℓ−1)` (`natDegree_shiftDet_of_extremal`), and
the determinant splits completely with multiplicities only `1` and `e+1`
(`shiftDet_of_extremal`):

    D_{i₀} = c · ∏_{Bad∖Z}(X−γ) · ∏_{Z}(X−γ)^{e+1},  c ≠ 0.

Moreover `coeff_shiftDet_top` identifies the top coefficient of `D_{i₀}` as
`det (scalarHankel e i₀ (f_{ℓ−1}))`, so extremality forces the *last word alone* to be
syndrome-nondegenerate of full Hankel rank (`det_scalarHankel_top_ne_zero_of_extremal`), in
particular at distance `> e` from the code (`not_isCloseOn_top_of_extremal`).

**Stability.**  With defect `δ = (e+1)(ℓ−1) − #Bad − e·|Z|`, the whole deviation is a cofactor of
degree `≤ δ`: `D_{i₀} = extremalFactor · R`, `deg R ≤ δ` (`exists_residual_of_defect`); the total
error-weight slack is `≤ δ` (`sum_witnessRadius_slack_add_le`); and `#(Z∖Bad) ≤ δ`
(`card_synZero_sdiff_add_le`).  The stability is linear with constant one, which is optimal.

**New proximity consequence.**  If `ℓ ≥ 2` and the top word agrees with a codeword off a set of
size `m ≤ e`, then (`card_badSetG_add_mul_card_synZero_add_le_of_close_top`)

    #Bad + e·|Z| + (e − m + 1) ≤ (e+1)(ℓ−1),

a strict improvement precisely in the regime a proximity-gap argument cares about.  The gain is
multiplicative along a *tail*: if the top `s` words all agree with codewords off one common set of
size `m ≤ e`, then `#Bad + e·|Z| + (e−m+1)·s ≤ (e+1)(ℓ−1)`
(`natDegree_shiftDet_add_le_of_close_top_block`,
`card_badSetG_add_mul_card_synZero_add_le_of_close_top_block`).

**Gate 3 exclusion.**  Taking `s = ℓ−1` shows that an extremizer is never a *rigid* family
(`not_rigidOn_of_extremal`): `RigidOn` is exactly the block hypothesis for the whole family, so
the extremal class is certified disjoint from the rigid phase of `SyndromeRigidityDichotomy.lean` — where the strictly
better bound `#Bad ≤ e(ℓ−1)` holds and is itself sharp.  The exclusion needs no counting
hypothesis and holds for every `e` and every size of `Z`.

**The bridge.**  The normal form of `shiftDet_of_extremal` is offset-independent up to a scalar,
so all offset determinants of an extremizer are proportional
(`shiftDet_associated_of_extremal`) and, for any two admissible offsets,
`deg gcd(D_{i₀},D_{i₁}) = (e+1)(ℓ−1)` (`natDegree_gcd_shiftDet_of_extremal`).  Flatness of the
offset-gcd hierarchy of §91 is therefore a *necessary condition* for extremality: the extremal
budget and the flat hierarchy are one phenomenon, a single degree-`(e+1)(ℓ−1)` polynomial dividing
every offset determinant, of which the collinear barrier family is the perfect-power special case.

**Barrier: extremizers are not unique.**  Both multiplicity patterns allowed by the normal form
are realised on families of opposite syndrome structure: the two-spike family attains the bound
with `Z = ∅` and squarefree determinant (`famSharp_extremal`), the collinear family attains it with
`Z = Bad` and determinant `c·L^{e+1}` (`famScaled_extremal`).  Hence the split factorisation is the
*minimal* common structure of the equality class, and no finer universal normal form exists.
Report: `docs/HANKEL_EXTREMAL_REPORT.md`.

## 93. RS-specific structure of the extremizers: localisation on `e+1` coordinates, the exact bad set, and a scalable extremizer (`Root/CodingTheory/HankelExtremalRSLocator.lean`, `Root/CodingTheory/HankelExtremalRSFamily.lean`, `Root/CodingTheory/HankelExtremalRSLocalised.lean`)

§92 closed the universal Hankel programme.  The question left open was whether the *Reed–Solomon*
structure of the witnesses — error locators inside the evaluation domain — can coexist with the
extremal determinant configuration.  It can, but only in one, completely rigid, way.

**Localisation.**  For any `ℓ` distinct bad challenges the Lagrange inverse of the trap lemma
(`isCloseOn_basis_of_forall_isCloseOn`) puts every word of the family close to the code off the
union of their witnesses, a set of size `≤ ℓe`.  In the redundancy regime `k + 2ℓe ≤ |D|` the
approximating codeword is independent of the chosen `ℓ` challenges (`unique_approx`), so the true
error set of each word lies in *every* such union.  A point of the intersection is therefore
covered by all but at most `ℓ−1` witnesses, and double counting gives
(`exists_common_support_of_le_card_badSetG`)

    |W| · (#Bad − (ℓ−1)) ≤ e · #Bad,      f_j close off W for all j < ℓ.

**Rigidity of the extremizers.**  At `#Bad = (e+1)(ℓ−1)` the count forces `|W| ≤ e+1` while the
Gate 3 exclusion of §92 forbids `|W| ≤ e`, so (`exists_common_support_of_card_badSetG_eq`) **every
extremizer is localised on exactly `e+1` coordinates**: a single error pattern of size `e+1`
shared by the whole family.  Contrapositive (`card_badSetG_lt_of_no_common_support`): a family
whose errors are *not* carried by `e+1` common coordinates satisfies the strictly better bound

    #Bad ≤ (e+1)(ℓ−1) − 1 .

The near-extremal band is covered by the dichotomy `card_badSetG_le_or_localised`: either
`#Bad ≤ e(ℓ−1)` (the rigid bound of §89, recovered here as the case `|W| ≤ e`), or the family is
localised on at least `e+1` coordinates.  There is no third possibility.

**The exact bad set of a localised family.**  Write `f_j = q_j + w_j` with `deg q_j < k` and `w_j`
supported on `W`, `|W| = e+1`, and let `E_y(X) = ∑_{j<ℓ} w_j(y)X^j` be the coordinate polynomial
of `y ∈ W`.  Support rigidity (`support_rigidity`: a word supported on `V` and agreeing with a
codeword on `S` vanishes on `S` whenever `|Sᶜ| + |V| + k ≤ |D|`) gives, under the sole
non-degeneracy hypothesis that some challenge keeps all `e+1` coordinates alive
(`badSetG_of_localised`),

    Bad = ⋃_{y ∈ W} { γ : E_y(γ) = 0 } .

Since `deg E_y ≤ ℓ−1` this re-proves `#Bad ≤ (e+1)(ℓ−1)` inside the localised class by pure
Reed–Solomon means (`card_badSetG_of_localised_le`) and exhibits the equality condition, proved in
`roots_errPoly_of_card_badSetG_eq`: at `#Bad = (e+1)(ℓ−1)` every `E_y` has exactly `ℓ−1` distinct
roots and the `e+1` root sets are pairwise disjoint, so each bad challenge kills exactly one
coordinate.

**The scalable extremizer.**  That condition is realisable for all parameters: with `|W| = e+1`
and pairwise disjoint `R y ⊆ F` of size `ℓ−1`, the multi-spike family `famMultiSpike`, carrying at
`x ∈ W` the coefficients of `∏_{r∈R x}(X−r)` and vanishing off `W`, has
`Bad = ⋃_{y∈W} R y` (`badSetG_famMultiSpike`), hence `#Bad = (e+1)(ℓ−1)`
(`card_badSetG_famMultiSpike`), and is localised on `W` (`isCloseOn_compl_famMultiSpike`).  For
`e = 1`, `ℓ = 2` it is the two-spike family of §90.

**Verdict.**  RS extremizers cannot be excluded — they exist for every `e` and every `ℓ` — but the
extremal locus is thin and completely classified: in the redundancy regime, extremality is
equivalent to localisation on `e+1` coordinates with split, pairwise disjoint coordinate
polynomials.  The usable proximity statement is the strict gain under the non-degeneracy
hypothesis.  Report: `docs/HANKEL_RS_LOCALISATION_REPORT.md`.

## 94. The critical bridge: the subresultant mechanism is void on the extremal locus (`Root/CodingTheory/HankelSubresultantBridge.lean`)

§93 classified the extremizers of the Hankel budget law: in the redundancy regime they are exactly
the families *localised* on a common set `W` of `e+1` coordinates, with coordinate polynomials
`E_y(X) = ∑_j w_j(y) X^j`.  The open question was whether the locator/Hankel description and the
elimination-theoretic `W_can` description of §§8x are two projections of one object.  They are
not — and the precise relationship is sharper and more useful than the conjectured identification.

**The closeness criterion.**  For a localised family of any arity `ℓ`, the combination `f_γ` is
`e`-close to the code **iff** some coordinate polynomial dies at `γ`
(`isCloseToCode_of_localised_iff`); unlike the bad-set computation of §93 this needs no
non-degeneracy hypothesis.

**The kernel collapse.**  Let `(Λ, Q)` be a Welch–Berlekamp kernel element of the localised line
`f₀ + Z f₁` over `F[Z]`, so `deg_X Λ ≤ e`, `deg_X Q < k + e`.  The residual
`P = Q − Λ·(q₀ + Z q₁)` still has `X`-degree `< k + e` and vanishes at every `x ∈ D ∖ W`, a set of
size `|D| − (e+1) ≥ k + e` in the regime `k + 2e + 1 ≤ |D|`.  Hence `P = 0`, and evaluating at a
coordinate `y ∈ W` gives

    Λ(Z, y) · E_y(Z) = 0 .

If no coordinate is degenerate (`E_y ≠ 0`) this forces `Λ(·, y) = 0` for all `e+1` coordinates
while `deg_X Λ ≤ e`, so `Λ = 0`: **the Welch–Berlekamp kernel of a nondegenerate localised line is
zero** (`wbKernel_locator_eq_zero_of_localised`).  Consequently `KernelNonzero` fails
(`not_kernelNonzero_of_localised`) and `W_can = 0` vacuously
(`W_can_eq_zero_of_localised`).

**Gate 4 breaks there.**  Since `W_can = 0`, its rational zero locus is all of `F`, while the close
locus has at most `e+1` elements (each `E_y` is linear for `ℓ = 2`).  So as soon as `e + 1 < |F|`
there are challenges in the zero locus of `W_can` that are not close
(`exists_root_W_can_not_close_of_localised`).  This upgrades the single `e = 0` counterexample of
`SubresultantCorrelatedBridge.lean` to a scalable family, for every `e` and every `k`: the
`KernelNonzero` hypothesis of the subresultant mechanism is not a technicality.

**Non-vacuity.**  The hypotheses are met by the explicit extremizers: the arity-2 multi-spike
family with one simple root per coordinate has zero Welch–Berlekamp kernel
(`not_kernelNonzero_famMultiSpike`).  So the degenerate phase is not an empty corner — it contains
the entire family that attains the sharp Hankel bound.

**Verdict on the bridge question.**  The two strongest MCA mechanisms of this project are
**complementary, not identical**.  The subresultant/elimination theory governs the regular phase
(nonzero kernel, `W_can ≠ 0`) and is provably blind on the localised/extremal phase; the
Hankel/locator theory computes the extremal phase exactly.  Together they cover the problem, and
the natural next hypothesis for a strictly stronger proximity theorem is exactly the one that
excludes the localised phase.

## 95. The phase separation, and what the Hankel hypothesis really assumes (`Root/CodingTheory/HankelKernelProximity.lean`)

§94 showed the Welch–Berlekamp kernel of a nondegenerate localised line vanishes.  Two further
consequences complete the picture.

**Extremality forces kernel collapse (and hence the contrapositive bound).**  At extremality
`#Bad = e+1` (the case `ℓ = 2` of the sharp bound) the family is localised on exactly `e+1`
coordinates, and no coordinate can be degenerate: dropping a degenerate coordinate would leave the
last word close to the code off a set of size `e`, which Gate 3
(`not_close_top_block_of_extremal`) forbids for an extremal family.  This is
`exists_nondegenerate_common_support_of_card_badSetG_eq`; feeding it to §94 gives, in
contrapositive form,

    shiftDet ≠ 0  and  KernelNonzero   ⟹   #Bad ≤ e      (`card_badSetG_le_of_kernelNonzero`)

with the probabilistic form `ε_mca ≤ e/|F|` (`epsMCAG_le_of_kernelNonzero`).  *Caveat.*  The joint
satisfiability of the two non-degeneracy hypotheses is **not** established; by the next paragraph
`shiftDet ≠ 0` excludes correlated agreement at radius `e`, which a nonzero Welch–Berlekamp kernel
is closely related to.  The demonstrably non-vacuous content of this circle is the forward
implication of §94, certified on the explicit extremizer family.

**The domain of the budget law.**  If the family has correlated agreement at radius `e` — one
common set `T`, `|T| ≤ e`, off which every word agrees with a codeword — then every challenge is a
root of the offset Hankel determinant, whose degree is at most `(e+1)(ℓ−1)`.  Over a field with
more than `(e+1)(ℓ−1)` elements this forces `shiftDet = 0`
(`shiftDet_eq_zero_of_common_close`).  Contrapositively:

    shiftDet ≠ 0   ⟹   the family has no common agreement set of co-size `e`
    (`not_common_close_of_shiftDet_ne_zero`).

So the non-degeneracy hypothesis carried by the whole Hankel budget-law programme is exactly the
statement that the family is *not* already correlated-agreeing at radius `e` — precisely the
non-trivial regime of a proximity gap, and never a hidden weakening of the theorems.

## 96. The rank profile of a matrix polynomial, and the budget law graded by the corank of the top word (`Root/CodingTheory/HankelRankProfile.lean`)

§92 leaves the top-degree behaviour of the offset Hankel determinant as a *binary* alternative:
the leading coefficient of `D_{i₀}` is `det (scalarHankel e i₀ f_{ℓ−1})`, so an extremizer has a
nonsingular top moment matrix, and a singular one costs *one* degree.  This section replaces the
alternative by a graded one, at the level of an arbitrary matrix polynomial.

**The mechanism — the column expansion.**  For `M : ℕ → Matrix (Fin n) (Fin n) F` put
`matPoly n ℓ M = ∑_{j<ℓ} X^j·M_j`.  Expanding the determinant multilinearly along the *columns*
(`det_matPoly_eq`) gives

    det (matPoly n ℓ M) = ∑_p (∏_s X^{p s}) · det (i, s) ↦ M_{p s} i s,

the sum over all choices `p : Fin n → {0,…,ℓ−1}` of one coefficient matrix per column.  The term
indexed by `p` has degree `n·d − q` with `d = ℓ−1` and *deficiency* `q = ∑_s (d − p s)`, so the
top `c` degrees of the determinant vanish as soon as every column-mixed matrix of deficiency `< c`
is singular (`natDegree_det_matPoly_add_le`).  This is a hypothesis-free vanishing criterion, and
two structural criteria follow from it.

**Criterion 1 — leading corank.**  If `rank M_{ℓ−1} ≤ r` then

    deg det (matPoly n ℓ M) + (n − r) ≤ n·(ℓ−1)        (`natDegree_det_matPoly_add_corank_le`).

A term of deficiency `q < n − r` takes more than `r` of its columns from `M_{ℓ−1}`; those columns
are then linearly dependent, so the mixed determinant vanishes.  The degree drops by the whole
*corank* of the leading coefficient matrix, not by one.

**Criterion 2 — the span profile.**  If for every `q < c` the columns of the top `q+1` coefficient
matrices `M_{ℓ−1−q},…,M_{ℓ−1}` together fail to span `F^n`, then again `deg det + c ≤ n(ℓ−1)`
(`natDegree_det_matPoly_add_le_of_span`).  The invariant that bounds the degree from above is the
first window size at which the accumulated top columns become spanning.  In the Hankel setting
this reads `#Bad + e|Z| + c ≤ (e+1)(ℓ−1)` whenever the moment columns of the top `q+1` words fail
to span `F^{e+1}` for every `q < c` (`card_badSetG_add_le_of_span`).

**The graded budget law.**  `hankelShift l e i₀ f` *is* the matrix polynomial of the scalar moment
matrices of the family (`hankelShift_eq_matPoly`), so Criterion 1 transfers verbatim:

    #Bad + e·|Z| + ((e+1) − rank (scalarHankel e i₀ f_{ℓ−1}))  ≤  (e+1)(ℓ−1)

(`card_badSetG_add_corank_le`, with the fully graded form `budget_law_corank` that also carries
the witness-radius slack).  Syndrome degeneracy of the last word is paid for in bad challenges.
Two consequences: the corank of the top moment matrix is at most the defect
`δ = (e+1)(ℓ−1) − #Bad − e|Z|` (`corank_scalarHankel_top_le_defect`), and an extremizer has a top
moment matrix of *full rank* `e+1` (`rank_scalarHankel_top_eq_of_extremal`) — the quantitative
form of `det_scalarHankel_top_ne_zero_of_extremal`.

**Closeness is only one way to lose rank.**  A word agreeing with a codeword off a set of size `m`
has moment matrix of rank at most `m` (`rank_scalarHankel_le_of_isCloseOn`): the annihilator
column operations, in their scalar form, kill `e+1−m` columns of the moment matrix, and
right-multiplication by a unimodular matrix preserves rank.  Equivalently *the rank of the
`(e+1)×(e+1)` moment matrix is a lower bound for the distance of the word to the code*.  Feeding
it to the graded law recovers the single-word Gate 3 gain

    #Bad + e|Z| + (e − m + 1) ≤ (e+1)(ℓ−1)          (`card_badSetG_add_le_of_isCloseOn_top`)

from a purely linear-algebraic hypothesis, so the same conclusion now holds for *any* mechanism
producing rank deficiency in the top word, not only closeness.

**Sharpness.**  The corank term is not slack.  If the top word vanishes and the truncated family
is extremal at length `ℓ−1`, the graded bound is attained with equality
(`card_badSetG_add_corank_eq_of_top_zero`), and this is realised explicitly by the two-spike
extremizer of §92 padded by a zero word
(`card_badSetG_add_corank_eq_padZero_famSharp`): `#Bad + e|Z| + corank = (e+1)(ℓ−1)` with
corank `e+1 = 2`.  The graded law therefore has extremizers that the ungraded law does not see,
and no term of it can be dropped.

All statements are proved in Lean with no `sorry` and no new axioms.

## 97. Cumulative rank charging: the coranks of all windows add, and the staircase proximity law (`Root/CodingTheory/HankelCumulativeRank.lean`)

§96 charged the corank of the moment matrix of the *top* word, and charged `1` per non-spanning
window.  The question left open was whether the rank deficiencies of *several* coefficient layers
can be charged **simultaneously**.  They can, additively, and the resulting law is sharp.

**The general law.**  For `matPoly n ℓ M = ∑_{j<ℓ} X^j·M_j` let `S_q` be the span of the columns of
the top `q+1` coefficient matrices.  Then

    deg det (matPoly n ℓ M) + ∑_{q<ℓ−1} (n − dim S_q) ≤ n(ℓ−1)

(`MatPoly.natDegree_det_matPoly_add_sum_le`).  In the column expansion, a nonvanishing term with
column `s` taken from `M_{p s}` must satisfy `#{s : ℓ−1−p s ≤ q} ≤ dim S_q` for every `q` at once,
and summing the complementary counts over the windows returns exactly the degree deficiency of the
term — each window is counted once, so nothing is double counted.  The leading-corank law of §96 is
the window `q = 0`; the span-profile law is the case where each window contributes `1`.  In the
Hankel setting this is `#Bad + e|Z| + ∑_{q<ℓ−1} ((e+1) − dim S_q) ≤ (e+1)(ℓ−1)`
(`card_badSetG_add_sum_le`).

**Proximity feeds the coranks.**  A word close to a codeword off `U` has *every* moment column in
the span of the `|U|` Vandermonde vectors of `U` (`col_scalarHankel_mem_span_of_isCloseOn`), so a
whole window of words close off one set `U` spans at most `|U|` dimensions
(`finrank_topColSpan_le_of_window_close`) — a joint statement, stronger than the per-word rank
bound of §96.  Hence the **staircase law** (`card_badSetG_add_staircase_le`): if the `t`-th word
from the top is close off `T_t` and `U_q = T_0 ∪ … ∪ T_q`, then

    #Bad + e·|Z| + ∑_{q<s} ((e+1) − |U_q|) ≤ (e+1)(ℓ−1).

Constant supports give back the Gate 3 charge `s(e−m+1)` (`card_badSetG_add_common_support_le`);
distinct singleton supports give the charge `∑_{q<s}(e−q) = s(e+1−s) + s(s−1)/2`
(`card_badSetG_add_singletons_le`, `staircase_gain_over_common_support`): unequal supports pay the
common-support charge *plus* a triangular term.

**Cash-out — the sparse-family regime.**  With `ℓ−1 ≤ e+1` and all words except the bottom one at
distance `1` with pairwise distinct error locations,

    2·(#Bad + e|Z|) ≤ ℓ(ℓ−1),      ε_mca ≤ ℓ(ℓ−1)/(2|F|)

(`card_badSetG_le_of_sparse_family`, `epsMCAG_le_of_sparse_family`): the decoding radius has
disappeared from the bound.  In the same regime Gate 3 gives only `#Bad ≤ (ℓ−1)²`, so the new law
is strictly stronger by the certified inequality `s(s+1) < 2s²` for `s ≥ 2`
(`sparse_bound_lt_common_support_bound`) — a factor tending to `2`, with the absolute gap
`s(s−1)/2` growing quadratically in the arity.  The hypothesis `shiftDet ≠ 0` is not vacuous:
evaluating the offset Hankel matrix at `X = 0` returns the moment matrix of the bottom word, so a
bottom word at distance `> e` certifies it (`shiftDet_ne_zero_of_det_scalarHankel_bot_ne_zero`,
`card_badSetG_le_of_sparse_family_of_bot`).

**Multi-word exclusion.**  An extremizer admits *no* window of top words with a common agreement
set of size `≤ e` (`not_window_close_of_extremal`); §96's "top moment matrix has full rank" is the
case `q = 0`.

**Sharpness.**  The two-spike extremizer padded by two zero words attains
`#Bad + e|Z| + (e+1) + (e+1) = (e+1)(ℓ−1)` (`card_badSetG_add_sum_eq_of_top_two_zero`,
`card_badSetG_add_sum_eq_padZeroTwo_famSharp`): two windows are charged their full corank at once
and the cumulative bound is met with equality, so the deficiencies genuinely add and no term can be
dropped.

No novelty is claimed for syndromes, Hankel matrices, key equations or Berlekamp–Massey/Padé
structure, which are classical; the new content is the additivity of window coranks with its
sharpness, the staircase law for unequal supports, the strict improvement over the previously
formalised common-support bound, and the multi-word extremizer exclusion.  Full discussion in
`docs/HANKEL_CUMULATIVE_RANK_REPORT.md`.  All statements are proved in Lean with no `sorry` and no
new axioms.

## 98. The two-word cash-out and the Hankel / subresultant bridge test

File: `RequestProject/Root/CodingTheory/HankelCumulativeRank.lean`.

**Δ-form of the staircase law.**  `card_badSetG_le_sub_staircase` states the multi-word proximity
result in the requested subtracted shape

    #Bad ≤ (e+1)(ℓ−1) − Δ,        Δ = ∑_{q<s} ((e+1) − |T_0 ∪ … ∪ T_q|),

with `Δ` explicit and read off the determinant column expansion.

**Two-word cash-out.**  At `ℓ = 2` the staircase law collapses to
`#Bad ≤ |T|` (`card_badSetG_le_card_support_two`): under `shiftDet ≠ 0`, the bad set of a two-word
line is bounded by the *error weight of the top word alone*, with no dependence on the rate `k` or
the decoding radius `e`.

**Bridge test.**  Compared against the project's subresultant/`W_can` route
(`Subresultant.card_badSet_le_unconditional`, `#Bad ≤ (k+1)e + 1`, hypothesis-free), the Hankel
bound is strictly smaller whenever the top word's error weight is at most `e`
(`two_word_hankel_lt_subresultant`).  The two mechanisms are therefore complementary rather than
equivalent: no reduction of one to the other was found and none is claimed.  Details in
`docs/HANKEL_CUMULATIVE_RANK_REPORT.md` §6.

## 99. The support-overlap phase law, and the limit of the staircase (`Root/CodingTheory/SupportOverlapPhase.lean`)

Files: `RequestProject/Root/CodingTheory/SupportOverlapPhase.lean`,
one theorem exposed in `RequestProject/Root/CodingTheory/PolynomialGeneratorMCA.lean`.
Full report: `docs/SUPPORT_OVERLAP_PHASE_REPORT.md`.
Reconnaissance: `analysis/support_overlap_staircase_probe.py`.

**The phase law.**  The incidence count behind the hypothesis-free bound `#Bad ≤ (ℓ−1)(e+1)` is
really a law in the size `M = |D| − |commonAgreement l f q|` of the *joint error support* of the
family (`card_badSetG_mul_defect_sub_le_of_common`):

    #Bad · (M − e) ≤ M · (ℓ−1).

It is worst at `M = e+1` and improves as the joint support grows:
`M ≥ e+2` already gives `#Bad < (ℓ−1)(e+1)` strictly (`card_badSetG_lt_sharp_of_defect_ge`), and
`M ≥ 2e` gives `#Bad ≤ 2(ℓ−1)` — a bound with **no dependence on the decoding radius**
(`card_badSetG_le_two_mul_of_defect_ge`).

**The law is exact.**  The block-spike family (`blockWord`): `g` blocks of `c` marked positions,
all positions of a block carrying one monic polynomial with `ℓ−1` prescribed roots.  For
`e = (g−1)c` it has `M = gc` and `#Bad = g(ℓ−1)` exactly
(`exists_blockWord_card_badSetG_eq`), i.e. `#Bad·(M−e) = M·(ℓ−1)`.  At `c = 1` this is the known
extremizer; at `g = 2` it certifies the radius-free bound `2(ℓ−1)` is attained.

**Large bad sets force minimal-union geometry.**  `#Bad = (ℓ−1)(e+1)` forces `M = e+1` exactly
(`defect_eq_of_card_badSetG_eq_sharp`), whence the unconditional dichotomy
(`card_badSetG_lt_sharp_or_exists_minimal_support`): in the window `k + (ℓ+1)e ≤ |D|`, either
`#Bad < (ℓ−1)(e+1)`, or the whole family agrees with one codeword family off a common set of
exactly `e+1` coordinates.

**Why the staircase cannot be globalised.**  The staircase charge `(e+1) − |T_0 ∪ … ∪ T_q|` is
positive only for unions of size `≤ e`, and the forced geometry sits one coordinate above that
threshold.  For the extremizer this is certified: the top word is at distance exactly `e+1` from
the code (`spikeWord_top_not_isCloseOn`), so every staircase charge is zero
(`spikeWord_staircase_charge_eq_zero`) and the staircase law degenerates to the plain budget law.
The certificate is scalable in `ℓ`, `e`, `k`.  Staircase and phase law act in opposite geometric
regimes (`M ≤ e` versus `M ≥ e+2`) and are complementary; a further improvement of `(ℓ−1)(e+1)`
cannot come from support geometry alone.

## 100. The `M = e+1` extremal phase: complete classification, and the end of the exclusion route (`Root/CodingTheory/MinimalSupportExtremalPhase.lean`, `Root/CodingTheory/MinimalSupportHankelBridge.lean`)

Files: `RequestProject/Root/CodingTheory/MinimalSupportExtremalPhase.lean`,
`RequestProject/Root/CodingTheory/MinimalSupportHankelBridge.lean`.
Full report: `docs/MINIMAL_SUPPORT_EXTREMAL_PHASE_REPORT.md`.
Reconnaissance: `analysis/minimal_support_extremal_phase_probe.py`.

**Badness is a root locus.**  In the minimal-support phase (`|T| = e+1`, window
`k + 2e + 1 ≤ |D|`, `ℓ ≤ |F|`), with the error-value polynomial
`P_x(X) = ∑_{j<ℓ} (f_j x − q_j(x)) X^j` (`errPoly`),

    γ bad  ⟺  P_x(γ) = 0 for some x ∈ T          (`mem_badSetG_iff_exists_errPoly_root`),
    Bad = ⋃_{x∈T} roots(P_x)                     (`badSetG_eq_biUnion_roots`),

whence the refined count `#Bad ≤ ∑_{x∈T} deg P_x` (`card_badSetG_le_sum_natDegree`) and
**top-word rigidity**: every coordinate of `T` at which the last word `f_{ℓ−1}` is uncorrupted
removes one bad challenge (`card_badSetG_add_card_topAgree_le_sharp`).

**Classification and stability.**  `#Bad = (e+1)(ℓ−1)` iff every `P_x` has exactly `ℓ−1` distinct
roots in `F` and the root sets are pairwise disjoint (`card_badSetG_eq_sharp_iff`); the
unconditional inverse theorem `exists_extremal_normal_form_of_card_badSetG_eq_sharp` adds that the
top word is corrupted at *every* coordinate of `T`.  Near-extremality propagates to each row:
`#Bad ≥ (e+1)(ℓ−1) − δ` forces every `P_x` to have at least `ℓ−1−δ` distinct roots
(`card_roots_errPoly_ge_of_card_badSetG`).

**No further invariant, and no exclusion by domain or challenge set.**  Over *any* RS domain, any
`T` of size `e+1` and any prescribed pairwise-disjoint root sets of size `ℓ−1` are realised by an
explicit family (`patternWord`, `card_badSetG_patternWord_eq_sharp`); ranks, minors,
proportionality and determinant conditions on the error matrix are all broken by extremizers, and
`T` is independent of the root pattern, so no relation coupling `E` to the locator `Λ_T` can hold.
Moreover for every challenge set `C` with `(e+1)(ℓ−1) ≤ |C|` there is an extremal family whose bad
set lies inside `C` (`exists_extremal_badSetG_subset`), and at `|C| = (e+1)(ℓ−1)` *every* challenge
of `C` is bad for it (`exists_badSetG_eq_challengeSet`).  The only surviving exclusion on the
challenge side is cardinality: `|F| < (e+1)(ℓ−1)` ⟹ `#Bad < (e+1)(ℓ−1)`
(`card_badSetG_lt_sharp_of_card_lt`).

**A protocol-side exclusion that does survive.**  If the top word `f_{ℓ−1}` is itself `e`-close to
the code, then `#Bad < (ℓ−1)(e+1)` strictly (`card_badSetG_lt_sharp_of_top_isCloseOn`).

**Hankel ↔ locator bridge (exact identity).**  For the `(e+1)×(e+1)` syndrome/moment matrix
`H(γ)_{i,j} = ∑_{x∈T} P_x(γ)·x^{i+j}`,

    det H(γ) = (∏_{x∈T} P_x(γ)) · det Vandermonde(T)²      (`det_syndromeMatrix_eq`),

so `γ` is bad iff `det H(γ) = 0` (`mem_badSetG_iff_det_syndromeMatrix_eq_zero`): the locator and
the Hankel/moment descriptions have literally the same zero locus, with the Vandermonde square as
the exact common factor.  Badness is thus decided by one determinant of size `e+1`, independent of
the code length.

**Only the top slot can be excluded** (`Root/CodingTheory/MinimalSupportSlotSharpness.lean`).  The
exclusion above is about the *leading* word, not about the batch.  The `±`-pattern family of arity
`3` — joint support `T` of size `e+1`, error-value polynomials `P_x(X) = (X − r_x)(X + r_x) =
X² − r_x²` — attains the sharp value `2(e+1)` while its slot-`1` word is identically zero, hence
literally a codeword (`card_badSetG_pmWord_eq_sharp`, `pmWord_one_eq_zero`,
`exists_extremal_with_codeword_slot`).  The configuration exists over `ZMod p` for every prime
`p > 2(e+1)` and every domain in the window (`exists_extremal_with_codeword_slot_zmod`), so this is
a genuine counterexample and not a vacuous statement.

---

## 101. Prize gap audit — "koalaIRS12" (no new theorems; measurement only)

Full write-up: `KOALAIRS12_PRIZE_GAP_AUDIT.md`; exact arithmetic in
`analysis/koala_irs_prize_gap_audit.py`.  Nothing in this section is a Lean statement.

The audited reduction is ArkLib's toy-problem certificate
`ε = (1−δ)^t + (ε_mca(C,δ) + |Λ(C^{⋈2},δ)|/|F|)·(1−(1−δ)^t)`, with challenges in
`KoalaBear.Ext6` (`log₂|F| = 185.93`) and `n = 2^16`.  Three measured facts:

1. **The MCA constant is worth 0 bits.**  Every bad-set bound proved here lies between `2^13` and
   `2^32`, so `ε_mca ≤ 2^-154` while the query term is `2^-67`; the certified score is unchanged
   to 30+ decimal places even at `#Bad = 0`.  A constant improvement first bites at the ceiling
   `−log₂((B+1)/|F|) ≈ 157` bits.  This applies to the sharp value `(ℓ−1)(e+1)`, the phase law,
   the Hankel/locator factorisation, staircase refinements, the top-word `−1`, and `#Bad ≤ |T|`.
2. **Only the radius reaches the score**, which equals `t·log₂(1/(1−δ))`.  The largest radius
   certified here is `δ ≤ (1−ρ)/2` (`Subresultant.card_badSet_le_unconditional`); ArkLib proves the
   same window admit-free with the better constant `n/|F|`
   (`ProximityGap.rs_mcaError_le_of_le_relUDR`, plus `mcaError_interleaved_eq` for interleaving),
   and its GKL bound `linear_mcaError_le_one_point_five_johnson` exceeds our radius at `ρ ≤ 1/8`.
   So no theorem here raises the certified score.
3. **The "top word close" hypothesis is not supplied by the protocol.**  The score's supremum runs
   over `ToyProblem.ViolatingInstance`, whose only hypothesis is that the *pair* violates the
   relaxed relation; `mcaError` quantifies over all word stacks.  Our own §100 family (codeword in
   one slot, sharp bad set) shows the configuration is realisable, so the conditional does not
   import — and it would be worth 0 bits if it did.

Decision: **C — mathematical gap remains.**  The prize-relevant target is any admit-free arity-2
MCA bound with `#Bad ≤ 2^98` at a radius strictly above `max((1−ρ)/2, 1−ρ^{1/3})`; `Δδ ≈ 0.0026` at
`ρ = 1/2` buys +1 bit at `t ≈ 200`, and the full Johnson radius `1−√ρ` is worth +17.2 bits there.

---

## 102. (ND′) refuted; the Johnson-radius chain repaired under (ND∃)

File: `RequestProject/Root/CodingTheory/NonDegeneracyExists.lean`.  Full decision log:
`JOHNSON_BRIDGE_DECISION.md`.

The Johnson-radius chain of §31 / §BCHKS carried the `∀`-form non-degeneracy hypothesis

    (ND∀) ∀ f₀ f₁, (badSet k e f₀ f₁).Nonempty → ∀ Q, LineInterpolant … Q →
            ∃ x₀, discLine bY x₀ Q ≠ 0.

**(ND∀) is false at both prize schedules.**  Three ingredients, all proved here:

1. *Interpolation is multiplicative.*  `GS.hasMultAt_mul`, `GS.wdegLt_mul`, `GS.zdegLe_mul`,
   and `LineInterpolant.sq`: if `Q₀` interpolates the formal line `f₀ + Z f₁` with
   `(L₀, m₀, bY₀, dZ₀)`, then `Q₀²` interpolates it with `(2L₀ − 1, 2m₀, 2bY₀, 2dZ₀)`.
2. *Squares are discriminant-degenerate.*  `discLine_eq_zero_of_isSq`: `discLine bY x₀ (S²) = 0`
   for every `x₀`; the degenerate constant case is `discRes_eq_zero_of_natDegree_eq_zero`
   (a zero derivative column in the Sylvester matrix).
3. *Lines with a bad point exist.*  `exists_badSet_nonempty`: the spike `f₀ = δ_{x₀}`,
   `f₁ = −f₀` has `γ = 1` bad whenever `1 ≤ k` and `k + e + 1 ≤ |D|`.

The halved schedule still meets the Guruswami–Sudan counting condition, via the sharpened
monomial count `2k·#monIdx(k,L) ≥ L² + kL` (`GS.card_monIdx_ge'`, `count_of_clean'`).  Hence
`nd_forall_false` and the two instances

| | `k` | `e` | `L` | `m` | `bY` | `dZ` | halved `L₀,m₀,bY₀,dZ₀` | margin |
|---|---|---|---|---|---|---|---|---|
| `nd_forall_false_rho_half` | 524288 | 306096 | 642769488 | 866 | 1225 | 1318349 | 321384744, 433, 612, 659174 | ×1.00048 |
| `nd_forall_false_rho_quarter` | 262144 | 523263 | 403177215 | 768 | 1537 | 1182344 | 201588608, 384, 768, 591172 | ×1.0000017 |

so `threshold_rho_half_bchks`, `threshold_rho_quarter_bchks` and the rest of the (ND∀) chain
are **vacuous as stated** (see `DISCREPANCIES.md` D91.1; nothing was deleted).

**The repair.**  The existential form `(ND∃)` — *some* interpolant of a line with a bad point
is non-degenerate — is not refuted by the square construction, and `epsMCAmax_le_disc_of_bad`
already takes it.  Re-derived under (ND∃) with the same constants:

* `epsMCAmax_le_of_schedule_exists` — the schedule packaging (the counting condition is no
  longer needed: the interpolant comes from the hypothesis);
* `threshold_rho_half_bchks_exists`, `threshold_rho_quarter_bchks_exists` —
  `ε_mca ≤ 2⁻¹²⁸` at `δ = 1 − √(ρ + 2⁻²⁰) − 2⁻¹⁰`, `n = 2²⁰`, `|F| ≥ 2¹⁶⁰`, `#Bad ≤ 2³²`.

(ND∃) is now the **single** remaining gap on the Johnson-radius route: proving it raises the
certified plain-RS proximity radius from `(1−ρ)/2` to `1 − √ρ − 2⁻¹⁰`, worth `+10.6` bits at
`ρ = 1/2` and `+40.8` bits at `ρ = 1/4` for a `t = 128` schedule, with no other change.

## 103. The exact barrier of the agreement-forcing mechanism

File: `RequestProject/Root/CodingTheory/ForcingBarrier.lean`.

Every unique-decoding-regime bound in this project — the Welch–Berlekamp/subresultant pencil,
`W_can`, the order-`e` syndrome recurrence, the top Hankel determinant, the cumulative Hankel
rank, the support/incidence extremal locus — runs through one common *forcing* step: two bad
challenges `γ ≠ γ'` determine, on `S_γ ∩ S_{γ'}` (guaranteed size `|D| − 2e`), a canonical
codeword pair `q₁ = (p_γ − p_{γ'})/(γ − γ')`, `q₀ = p_γ − γ q₁`, and the argument needs that
pair to be the same for all choices — i.e. uniqueness of interpolation on `|D| − 2e` points.

* `forcing_unique_at_frontier` — for `k + 2e ≤ |D|` the pair is unique.
* `exists_two_interpolants_of_card_lt` — on any set of fewer than `k` points, and for any
  prescribed data, `p` and `p + ∏_{x∈S}(X − x)` are two distinct polynomials of degree `< k`
  realising it: interpolation is never determined.
* `forcing_not_unique_beyond_frontier` — hence for `|D| < k + 2e` the forcing step has no
  output at all on a set of the guaranteed size.
* `forcing_guaranteed_size_ge_iff` — the switch is exactly at `k + 2e = |D|`, i.e.
  `δ = (1−ρ)/2`.

This is a rank/degree obstruction on the *mechanism*, not a refutation of MCA beyond
`(1−ρ)/2` and not a lower bound on `#Bad` (see `DISCREPANCIES.md` D91.2).  It is the precise
reason a Johnson-range route must replace "one codeword" by "an interpolation object for the
whole line" — which is what the Guruswami–Sudan interpolant of §102 does, and why the only
thing missing there is its non-degeneracy.

## 104. Bluestein's chirp transform: an arbitrary-length DFT as one cyclic convolution (`RequestProject/Bluestein.lean`)

Every fast transform formalised so far in this project constrains the length: Cooley–Tukey
and split radix want `2^k`, Good–Thomas wants coprime factors, Rader wants a prime.  Bluestein
constrains nothing.  With `ω² = ζ` and the chirp `i ↦ ω^{i²}`, the identity
`ζ^{ij} = ω^{i²}·ω^{j²}·ω^{−(i−j)²}` turns the transform into a correlation, and padding turns
the correlation into a cyclic convolution of **any** length `L ≥ 2n − 1`:

* `FFT.dft_eq_chirp_conv` — for every `j < n`,
  `DFT_n(a)_j = ω^{j²} · (chirpIn ⊛_L chirpKer)_j`, where `chirpIn` is the input weighted by
  the chirp and zero-padded and `chirpKer` is the `L`-periodic kernel supported on `±m`,
  `m < n`.  No hypothesis on `n` is used; the only field hypothesis is that `ζ` has a square
  root `ω ≠ 0`.
* `FFT.sq_root_of_odd` — for odd `n` a square root always exists inside `⟨ζ⟩`, namely
  `ζ^{(n+1)/2}`, so no field extension is ever needed at odd lengths
  (`FFT.dft_eq_chirp_conv_odd`).

Why this matters over `M31`.  The base field has no root of unity of order `2^k`, `k ≥ 2`, and
none of order 30 or 62; the free choice of `L` sidesteps all of that:

* `FFT.M31.dft31_eq_chirp_conv63` — the length-31 transform (`ζ = 2`) is **one cyclic
  convolution of length 63**, and `63 = 9·7` divides `p − 1`, so that convolution is a
  base-field problem (three length-63 transforms by `FFT.dft_inv_pointwise_mul`, whose root
  exists by `FFT.M31.exists_primitiveRoot_sixtythree`, or a Good–Thomas `9 ⊗ 7` product).
* `FFT.M31.chirp31_is_rotation`, `FFT.M31.chirpKer63_is_rotation` — at this length the chirp
  is `ω = 2^16`, so *every* chirp constant, in the input weighting, in the output weighting
  and in the kernel, is a power of two, i.e. a bit rotation (`FFT.M31.mul_two_pow_eq_rotate_M31`).
  The Bluestein overhead at length 31 over `M31` therefore contains no general multiplication
  at all.

* `FFT.M31.dft151_eq_chirp_conv693` — the payoff at a *rough* length: 151 is a prime factor of
  `p − 1`, so the length-151 transform exists over `M31` but none of the recursive schemes
  applies to it; Bluestein turns it into a cyclic convolution of length `693 = 9·7·11`, which
  is smooth, divides `p − 1` (`FFT.M31.exists_primitiveRoot_sixninetythree`) and splits into
  pairwise coprime factors for Good–Thomas.

Caveat: this is a correctness result plus a structural observation about the constants; no
operation count for Bluestein is defined here, and no benchmark was run.

## 105. Radix 4: the missing column of the twiddle-count comparison (`RequestProject/Radix4.lean`)

`SplitRadix.lean` compared radix 2 with split radix in a fixed cost model (multiplications by
fourth roots of unity are free, twiddle tables precomputed, additions not counted) and left
radix 4 open (`DISCREPANCIES.md` O3).  This file closes that column in the *same* model.

* `FFT.dft_radix4` — the radix-4 step is `dft_dif` at `d = 4`; `FFT.dft_radix4_zero` records
  that the `r = 0` branch has no twiddles.
* `FFT.radix4_free_odd_branch` — in the branches `r` coprime to `m` (i.e. `r = 1, 3` at
  `m` a power of two) the only free twiddle is at `s = 0`: `m − 1` multiplications each.
* `FFT.radix4_free_even_branch` — in the branch `r = 2` with `m = 2m'` the free twiddles are
  exactly `s = 0` and `s = m'`: `m − 2` multiplications.
* Hence `3m − 4` per radix-4 level (`FFT.radix4_step_count`) against `4m − 4` for the two
  radix-2 levels it replaces (`FFT.radix4_step_lt_two_radix2_steps`), giving the recursion
  `radix4Cost (k+2) = 4·radix4Cost k + (3·2^k − 4)`.
* `FFT.radix4Cost_le_radix2Cost`, `FFT.radix4Cost_lt_radix2Cost` — radix 4 is never worse, and
  is strictly better for every `k ≥ 4`.
* `FFT.splitRadixCost_le_radix4Cost` (via `FFT.two_mul_splitRadixCost_le`) — split radix is
  never worse than radix 4, so the three schemes are linearly ordered in this model:
  `S ≤ R₄ ≤ R₂`.
* `FFT.radix4_cost_table` — for `k = 0 … 8`: `R₂ = 0,0,0,2,10,34,98,258,642`;
  `R₄ = 0,0,0,2,8,28,76,204,492`; `S = 0,0,0,2,8,26,72,186,456`.

Model caveat unchanged: these are counts of the *recursions* in the stated model, justified by
the identity and the free-twiddle classification, not extracted from a formal program object,
and no benchmark was run.  Radix 8 remains unformalised.

## 106. Radix 8: the last column, and why it loses in this model (`RequestProject/Radix8.lean`)

The same analysis as §105, one radix up, together with a reusable criterion.

* `FFT.four_pow_eq_one_iff` — for `ζ` primitive of order `4N`, `ζ^e ∈ μ₄ ↔ N ∣ e`.  Every
  free-twiddle classification of the development is an instance of this.
* Free twiddles of a radix-8 level at length `8m`, `m = 2^j`: the branch `r = 0` is entirely
  free (`radix8_free_zero_branch`); the four odd branches and the branches `r = 2`, `r = 6`
  have only `s = 0` free (`radix8_free_odd_branch`, `radix8_free_two_branch`,
  `radix8_free_six_branch`); the branch `r = 4` has `s = 0` and `s = m/2`
  (`radix8_free_four_branch`).  Total `7m − 8` per level (`radix8_step_count`), plus `m`
  eight-point butterflies at `radix2Cost 3 = 2` each.
* `FFT.radix8Cost_le_radix2Cost` — radix 8 is never worse than radix 2;
  `FFT.radix4Cost_le_radix8Cost` — but never better than radix 4.  With §105 the family is
  linearly ordered in this model: `S ≤ R₄ ≤ R₈ ≤ R₂`, e.g. at `n = 64` the counts are
  `72 ≤ 76 < 80 < 98` (`radix4_lt_radix8_at_six`, `radix8_cost_table`).

The verdict is model-relative and is stated as such: the model charges one unit for *every*
multiplication by a constant outside `μ₄`, so it cannot see that the eighth roots
`ω₈^{±1}, ω₈^{±3}` are cheaper than a generic twiddle — which is precisely the effect a real
radix-8 kernel exploits.  No implementation claim and no benchmark.

## 107. The two radix-2 routes over `M31`, compared (`RequestProject/ExtensionVsCircle.lean`)

`M31` has no `2^k`-th root of unity for `k ≥ 2`, so a radix-2 transform of length `2^k` must
either move to `𝔽_{p²}` or stay in the base field and use the circle group.  Both were already
formalised; this file compares them in one model, counting multiplications in the **base**
field.

* `FFT.extRadix2_correct` — the extension route: for every `k ≤ 32` there is a primitive
  `2^k`-th root of unity in `𝔽_{p²}` and the radix-2 recursion computes the DFT with it.
* The butterfly counts agree: `2·Tree.imulCount k = k·2^k = 2·fftMulsOpt k`.  What differs is
  the price of one multiplication: exactly three base multiplications in `𝔽_{p²}`, by
  `FFT.Bilinear.M31sq_bilinear_complexity` (three suffice and two never do).
* `FFT.extBaseMuls_eq_three_mul` — hence `extBaseMuls = 3 · circleBaseMuls`;
  `FFT.circle_lt_ext_baseMuls` — the circle route is strictly cheaper for every `k ≥ 1`;
  `FFT.circle_lt_ext_packed` — and still cheaper by `3/2` against the packing trick that
  carries two base-field transforms in one extension transform.
* `FFT.baseMuls_table` — per transform of `2^k` points, `k = 0 … 8`:
  circle `0, 1, 4, 12, 32, 80, 192, 448, 1024`; extension `0, 3, 12, 36, 96, 240, 576, 1344, 3072`.

Caveats: multiplications only — additions, memory traffic (extension data are twice as large)
and implementation effects are outside the model, and no benchmark was run.

## 108. Curve lines, the degeneracy threshold `K*`, and the death of (DICH) (`RequestProject/Root/CodingTheory/CurveLineDegeneracy.lean`)

The Johnson-chain bottleneck mining (`JOHNSON_MIN_J_REPORT.md`) traced the conditional
`ε_MCA` theorems back to their first algebraic consumer and found that
`eval_discLine_eq_zero_of_isBad` discards the `¬ LineCloseOn` conjunct of `IsBad`, so the
chain in fact bounds the *close* set rather than the bad set.  (ND∃) is therefore stronger
than the chain consumes — but so is every weakening of it inside that paradigm.

* `curveLine_sq_dvd` — for a *curve line* `f₀ = a|_D`, `f₁ = b|_D` with `deg a, deg b ≤ K`,
  **every** admissible interpolant is divisible by `(Y − (a + Z·b))²`, provided the two
  enlarged budgets `L + (K+1−k)·bY ≤ m|D|` and `L + (K+1−k)·bY − (K+1) ≤ (m−1)|D|` hold.
  The enlargement is `wdegLt_weight_le`: a `(k,L)`-admissible `Q` of `Y`-degree `≤ bY` is
  `(k', L + (k'−k)bY)`-admissible.  Hence `curveLine_not_separableInY`.
* `curveLine_card_polyAgreement_le` — curve lines are *far* from the codeword-line variety:
  any codeword agrees with `b|_D` on at most `K` positions.  With the previous item this
  gives `dichFar_fails`: **(DICH) is false**, at both prize schedules
  (`dichFar_fails_rho_half`, `dichFar_fails_rho_quarter`, `|D| = 2^20`, `K = k`).
* `curveLine_card_badSet_le_one` — and yet curve lines are harmless: if `K + e < |D|` then
  they have at most one bad challenge, unconditionally (no interpolation, no schedule).
  `curveLine_isBad_zero` shows the bad challenge is really there.
* `degeneracy_threshold_lt_witness_size` — the arithmetic behind the coincidence: the
  forced-degeneracy threshold `K* ≈ k + k·e/t` satisfies `K* < t ⟺ k|D| < t² ⟺ t > √(k|D|)`,
  i.e. exactly the Johnson condition.  Numerically `K* = 740604 < t = 742480` at `ρ=1/2`.
* `card_badSet_le_of_annihilator_family`, `epsMCA_le_of_annihilator_family` — the counting
  step of the proposed repair: a family of `N` nonzero annihilators of degree `≤ d` gives
  `#Bad ≤ N·d` and `ε_mca ≤ N·d/|F|`.  Exact budget (`analysis/min_j_budget.py`): the
  family-of-`|D|` repair costs `2^40.34` against `B_max = 2^57.93` at the actual KoalaBear
  sextic field, but exceeds the `2^32` allowed by the repository's `|F| ≥ 2^160` hypothesis.

No Johnson-radius theorem is claimed.  The report records the target's value
(`Δδ = +0.114792` at `ρ=1/2`, `+27.745` bits at 128 queries) as a target, not an achievement.

## 109. The Johnson-radius structural dichotomy (`RequestProject/Root/CodingTheory/JohnsonStructuralDichotomy.lean`)

Full account: `JOHNSON_STRUCTURAL_DICHOTOMY_REPORT.md`.  All statements below are sorry-free
and use only `propext`, `Classical.choice`, `Quot.sound`.

* `johnson_escape_or_structure` — **unconditional dichotomy**, no budget, schedule or
  non-degeneracy hypothesis: for every line and every threshold `c`, either the badness
  witnesses form a Johnson set family (`#Bad·(t² − |D|·c) ≤ |D|·t`, informative at `c = k`
  exactly when `k|D| < t²`, i.e. at the Johnson radius), or some codeword pair has common
  agreement `|T| ≥ c+1` *and* explains two distinct bad challenges.
* `card_explainedSet_le` — for **every** codeword pair,
  `#{γ explained} + |T| ≤ |D|`; the residual witness sets `S_γ \ T` are nonempty and pairwise
  disjoint.  `unexplainedBadSet_eq_empty_of_large_pair` — once `|T| ≥ k+e` every bad
  challenge is explained, so `#Bad ≤ |D| − |T|`; this re-derives the near half of the
  near/far dichotomy by pure disjointness.
* `card_inter_lt_of_not_explained` — an unexplained bad challenge meets `T` in `< k` points,
  with *every* one of its witness sets.
* `exists_pair_explaining_of_isBad`, `card_badSet_le_of_explaining_family` — the covering
  reformulation: every bad challenge is explained by some pair with `|T| ≥ k`, and
  `#Bad ≤ Σ_P (|D| − |T_P|) ≤ (#pairs)·(|D| − k)`.  The Johnson-radius question is exactly
  *how many codeword pairs are needed to explain one line*.
* `GapBound` + `card_badSet_le_of_gapBound` + `epsMCAmax_le_johnson_of_gapBound` — the single
  remaining lemma (bound the unexplained bad challenges of a pair with
  `c+1 ≤ |T| < k+e`) and the Johnson-radius bound it implies.
* `escape_rho_half_delta_gt_quarter` — **unconditional**: at `|D| = 2²⁰`, `k = 2¹⁹`,
  `e = 262145` (`δ = 0.2500009… > 1/4`, `t² − |D|k = 68717903873 > 0`), a line with no
  codeword pair explaining two bad challenges on `> 2¹⁹` common positions has `#Bad ≤ 13`.
* `johnson_rho_half_delta_quarter` — **conditional on `GapBound`** with any `Bgap ≤ 2³¹`:
  `ε_mca ≤ 2⁻¹²⁸` at that schedule for `|F| ≥ 2¹⁶⁰`.

The unconditionally certified radius is **unchanged** (`δ = 0.177124…` at `ρ = 1/2`,
`nearFar_rho_half`); the `δ > 1/4` statement is conditional.

## 110. The exact locator law for the syndrome Hankel kernel (`RequestProject/Root/CodingTheory/HankelLocatorKernel.lean`)

For a moment (syndrome) sequence `S r = ∑_{x∈E} a_x x^r` with nonzero amplitudes, and the
`rows × cols` Hankel matrix `H i j = S(i+j)` whose kernel vectors are read as polynomials of
degree `< cols`:

* `eq_zero_of_moments_vanish` — Vandermonde annihilation: `|E|` vanishing moments of a weight
  function supported on `E` force it to vanish.
* `eval_eq_zero_of_hankelRel`, `supportLocator_dvd_of_hankelRel` — **the Vandermonde locator
  lemma**: `rows ≥ |E|` forces every kernel vector to vanish on `E`, i.e. `Λ_E ∣ L`.
* `hankelRel_iff_locator_mul` — **the kernel factorisation** `ker H = Λ_E · F[X]_{< cols−|E|}`
  in that range; with `cols = e+1` this is the conjectured `ker H = Λ_E · F[X]_{≤ d}`.
* `hankelRel_iff_values`, `hankelRel_iff_seed_decomposition` — the **complete** kernel
  description for *any* row count: `L ∈ ker H` iff `a_x L(x) = R(x)·v_x` on `E` for some
  `deg R < |E| − rows`, i.e. `ker H = { (R·L₀ mod Λ_E) + Λ_E·G }` with `L₀` the interpolant of
  `x ↦ v_x/a_x`.  Kernel dimension `cols − rows`, of which `|E| − rows` directions are
  non-locators.
* `exists_hankelRel_nonvanishing`, `exists_minimal_hankelRel_not_locator` — **sharpness**: as
  soon as `rows < |E| ≤ cols` there is a kernel vector of degree `< |E|` vanishing nowhere on
  `E`; being of degree `< deg Λ_E`, the *minimal-degree* kernel vector is a non-locator.
* `hankelKernel_locator_law_iff` — the two combined: every kernel vector is a locator **iff**
  `rows ≥ |E|`.
* `defect_two_schedule`, `defect_schedule_general`, `hankelRel_first_boundary` — the index
  arithmetic of the MCA pencil (`rows = n−k−e = e−d`, `cols−rows = d+1`) and the explicit
  first boundary layer.

Consequence for the Johnson programme (`DEFECT2_KERNEL_REPORT.md`): at
`(n,k,e) = (2²⁰, 2¹⁹, 262145)` the locator lemma covers exactly `|E| ≤ e−2` and the two
layers `|E| ∈ {e−1, e}` are *provably* out of reach of any kernel-only argument, minimality
included.  No new certified radius; the `δ > 1/4` schedule statement remains conditional.

## 111. The MCA two-syndrome gate: two channels, never a common support (`RequestProject/Root/CodingTheory/TwoSyndromeGate.lean`)

Can the MCA data of a line supply *two* syndrome channels with the **same** error-location
support, so that an `s = 2` interleaved / simultaneous-partial-inverse locator recovery could be
run?  The answer is negative, and every step of it is machine-checked
(`TWO_SYNDROME_GATE_REPORT.md`; exact probes `analysis/two_syndrome_gate_probe.py`,
`analysis/two_syndrome_gate_pi_failures.py`).

* `channel_affine_combination`, `channelSpan_eq_span_pair` — **channel collapse**: the syndrome
  of every challenge is `H f₀ + γ·H f₁`, and the span of *all* challenge channels is exactly
  `span {H f₀, H f₁}`.  Two channels exist, and there is provably no third: the interleaving
  order available to MCA is exactly `s = 2`.
* `badWitness_ne` — two distinct bad challenges can never share a witness set (one line from the
  existing small-union rigidity `lineCloseOn_of_two_close_on`).
* `eq_zero_of_two_cancellations`, `channelSupport_ne_of_cancels`, `jointSupport_eq_union` —
  badness is a *cancellation* event, cancellation sets of distinct challenges are disjoint, so
  the two channel supports are always different (often disjoint) and only their union
  `E₁ ∪ E₂ = E`, of size up to `2e`, is common.
* `exists_correlatedPair_of_commonSupport` — conversely a genuine common support already yields
  a correlated pair by inverting a `2 × 2` system: the success branch of the route is circular.
* `twoChannelBudget_iff`, `twoChannel_rate_half_threshold` — the `s = 2` budget for a support of
  size `m` is `3m + 1 ≤ 2(n−k)`; with `m = 2e` and rate `1/2` it forces `6e < n`, i.e. `δ < 1/6`,
  below the `δ = 1/4` baseline.  At both project schedules the stacked system is empty
  (`defectTwo_stacked_system_empty`, `safeJohnson_stacked_system_empty`).
* `GateCounterexample.*` — the smallest exact instance: `GF(3)`, `n = 3`, `k = 1`, `e = 1`,
  `f₀ = (0,0,1)`, `f₁ = (0,1,0)`; the challenges `0` and `1` are both bad with **disjoint**
  channel supports `{2}`, `{0}`, union of size `2 = 2e = n − k`, hence zero rows per channel.

Exact FULL-MCA testing (3 364 267 genuine bad-challenge pairs, exhaustive for `GF(3), |D|=3` and
`GF(5), |D|=4`): `E₁ = E₂` in **0** cases, disjoint supports in 1 940 608, channel span always
`span{H f₀, H f₁}`, empty stacked system in 96.8 %; where the system is nonempty, stacking adds
rank in 99.97 % and simultaneous locator recovery succeeds in 90.8 %, the in-budget failures being
a stacked block-Hankel rank deficiency `rank = m − 1` (all maximal minors vanish) with error-value
rank still 2.  Verdict: **KILL** for the two-syndrome route to Johnson MCA.

## 112. Core/fibre charging and the fold pencil: the `e+1` cap is a `κ ≥ 3e` phenomenon (`RequestProject/Root/CodingTheory/CoreFibreCharging.lean`, `RequestProject/Root/CodingTheory/FoldPencil.lean`)

Full account in `IRREGULAR_CORE_FIBRE_REPORT.md`.

* `CoreCharge.card_mul_le_card_support`, `CoreCharge.card_le_succ_of_lt_core` — the
  replacement for the refuted per-challenge free-challenge cap: for the challenges of one
  *codeword-line component*, with `m = |supp u₁|` and `b = |{x : u₁ x = 0, u₀ x ≠ 0}|` the
  common core, `|component| · (m + b − e) ≤ m`, hence `|component| ≤ e + 1` whenever
  `e < m + b`.  The shared core is charged **once**, not once per challenge.  Sharp: the
  common-window pencil attains it with `m = e+1`, `b = 0`.
* `isBad_fibrePencil`, `card_fibreBad_le_succ`, `card_fibreBad_le_of_uniform_fibres` —
  generalised common-window pencils `f₁ = 1_Y`, `f₀ = −h(x)·1_Y` are classified by the
  fibres of the twist `h`: a challenge is bad iff its fibre in `Y` is nonempty and misses at
  most `e` positions, distinct challenges have disjoint fibres, so `#Bad ≤ e + 1`, and with
  uniform fibres of size `d` only `⌊e/d⌋ + 1`.  Raising the degree of the twist strictly
  *hurts*; degree one is extremal.
* `isBad_foldPencil`, `card_le_card_badSet_foldPencil` — **the fold pencil.**  If the domain
  contains `t` pairwise disjoint blocks `E i` of size `e` that are the fibres of a degree-`e`
  fold (`∏_{y∈E p}(x−y) = u q − u p` for `x ∈ E q`), then with `W = ∏_{x ∉ E a ∪ E b}(X−x)`,
  `f₀ = W·1_{E a}`, `f₁ = W·1_{E b}` every third block gives a bad challenge
  `γ_i = (u a − u i)/(u b − u i)` with window `D ∖ E i` and witness
  `(u a − u i)·∏_{x ∉ E a ∪ E b ∪ E i}(X−x)`.  Hence `#Bad ≥ t − 2`, valid exactly when
  `|D| < k + 3e` and `k + 2e ≤ |D|`, i.e. on the band `2e ≤ κ ≤ 3e − 1`.
* `exists_foldPencil_multiplicative` — concrete degree-`e` model: `D` a union of `t` cosets
  of `μ_e`, fold `x ↦ x^e`; `#Bad ≥ t − 2 = |D|/e − 2` for every rate in the band.
* `foldPencil_e_eq_one`, `sub_two_div_card_le_epsMCAmax_of_e_eq_one` — for `e = 1` the fold
  hypothesis is automatic, so **every** Reed–Solomon code with `k = |D| − 2` (`κ = 2 = 2e`,
  the unique-decoding boundary) has a line with `|D| − 2` bad challenges and therefore
  `ε_mca ≥ (|D| − 2)/|F|`, against the cap `e + 1 = 2` valid for `κ ≥ 3`.

Consequence: the hypothesis `3e < κ + 1` of `card_badSet_le_succ_radius` is **sharp** and
cannot be relaxed to unique decoding.  Exhaustive small-field confirmation: smallest band
violation `q = 11, |D| = 8, k = 3, e = 2` with `#Bad = 4 > 3`.

## 113. The capacity-gap pencil: the bad set is exponential near capacity (`RequestProject/Root/CodingTheory/CapacityGapPencil.lean`, `RequestProject/Root/CodingTheory/CapacityGapCosets.lean`)

Write `c = |D| − k − e = κ − e` for the **capacity gap** in absolute coordinates, so that
`η = 1 − ρ − δ = c/|D|`.  All previously known lower bounds on the MCA bad set were linear in
`|D|` (`ε_mca ≥ (e+1)/|F|`, `≥ (|D|−2)/|F|`).  This section gives exponential ones and, at
`c = 1`, the exact maximum.  Full discussion in `CAPACITY_GAP_REPORT.md`.

* `prod_pow_sub_C_shape` — a product of `s+1` binomials `X^c − b_i` equals
  `X^{c s + c} − (Σ b_i)·X^{c s} + (degree < c s)`.
* `isBad_powerPencil` — if the vanishing polynomial of a window `S` has the shape
  `X^{k+c} + γ·X^k + (degree < k)` then `γ` is bad for the power pencil `f₀ = x^{k+c}`,
  `f₁ = x^k`: the line point interpolates on `S`, while the direction `x^k` cannot
  (it would need a degree-`k` polynomial with `|S| = k+c > k` roots).
* `card_badSet_ge_blocks` — **the capacity-gap pencil.**  If `D` contains `m` disjoint blocks
  of size `c` with binomial vanishing polynomials `X^c − b_i` and the `(s+1)`-subset sums of
  the `b_i` are distinct, then with `k = c·s` and `e = |D| − k − c`
  `#Bad ≥ C(m, s+1) = C(|D|/c, k/c + 1)`.
* `card_badSet_le_choose_succ_dim` — the matching **universal** upper bound: whenever
  `k + 1 + e ≤ |D|` (gap `c ≥ 1`), every line has `#Bad ≤ C(|D|, k+1)`, which at `c = 1` is
  `C(|D|, e)`.  Proof: shrink each witness to a `(k+1)`-window on which the direction is not
  interpolable (`isCloseOn_of_forall_card_subset`); two challenges cannot share such a
  window.  (For `c ≥ 2` the circuit bound `card_badSet_le_circuit` is stronger by the factor
  `C(k+c−1, k)`; at `c = 1` that factor is `1`.)
* `card_badSet_eq_choose_gapOne`, `card_badSet_twoPowDomain` — on a domain with distinct
  `(k+1)`-subset sums (e.g. `{1,2,4,…,2^{m−1}} ⊆ ZMod p`, `2^m < p`) the power pencil attains
  it: `#Bad = C(|D|, k+1)` **exactly**.  So the window-free binomial bounds of
  `CircuitIncidence.lean` are sharp at `c = 1`.
* `two_pow_card_le_mul_card_badSet_twoPowDomain`, `choose_div_card_le_epsMCAmax_twoPowDomain` —
  with `|D| = n = 2(k+1)`, `e = k+1`: `2^n ≤ n·#Bad` and `ε_mca ≥ C(n,e)/|F|`.
* `card_badSet_ge_cosets`, `exists_capacityGap_counterexample` — the same at **every** gap
  `c ≥ 1`, on `D = ⋃_{i<m} 2^i·μ_c ⊆ ZMod p` with `c ∣ p−1`, `2^{cm} < p` (such primes exist
  by Dirichlet, `exists_prime_coset_parameters`): `#Bad ≥ C(m, s+1)`, i.e. `exp(Θ(1/η))`.

Consequence: **the Grand-MCA/proximity statement in the form `ε_mca ≤ poly(|D|)/|F|` for all
`δ < 1 − ρ` is false**, already at `δ = 1 − ρ − 1/|D|`; any true bound must grow at least like
`exp(Ω(1/η))` in the gap to capacity, and can be polynomial only for `c = Ω(|D|/log|D|)`.
Nothing in the Johnson regime, in unique decoding, or at a constant gap `η` is affected: at
constant `η` the construction only yields `O(1)` bad challenges, and whether `#Bad` can be
superpolynomial there is the open question left by this section.

## 114. The subspace pencil: `#Bad` beats every fixed polynomial at some vanishing capacity gap (`RequestProject/Root/CodingTheory/AdditivePolynomial.lean`, `RequestProject/Root/CodingTheory/SubspaceFamily.lean`, `RequestProject/Root/CodingTheory/SubspacePencil.lean`, `RequestProject/Root/CodingTheory/IndicatorLineList.lean`)

> **Corrected heading.**  This section previously read "`#Bad` is superpolynomial at every
> vanishing capacity gap".  The Lean theorem is an *existence* statement, and the stronger
> reading is false for this family; see §116 and `D114.2` in `DISCREPANCIES.md`.

Full write-up: `SUBSPACE_PENCIL_REPORT.md`.  Numerical check: `analysis/subspace_pencil_check.py`.

Notation as in §113: `n = |D|`, `c = n − k − e` the absolute capacity gap, `η = c/n`.

The capacity-gap pencil of §113 gives `#Bad ≥ C(n/c, k/c + 1)`, which is `exp(Θ(1/η))` at
fixed `c` but collapses to `O(1)` once `c = Θ(n)`.  It therefore suggested a *gap-layer law*
`max #Bad ≍ poly(n) + exp(Θ(1/η))`, i.e. polynomial behaviour outside the boundary layer
`c = O(n/log n)`.  **That law is false.**

**The construction.**  Over a field of characteristic `p`, let `U ⊆ F` be an `F_p`-subspace of
dimension `m` and `w ∉ U`.  Put `D = U ∪ {w}`, `n = p^m + 1`, `k = p^{ℓ−1}+1`,
`e = n − p^ℓ − 1`, so `c = p^ℓ − p^{ℓ−1}`, and take the line

```
f₀(x) = x^{p^ℓ},   f₁ = 1_{\{w\}} .
```

For every `ℓ`-dimensional subspace `V ≤ U` with subspace polynomial `L_V = ∏_{v∈V}(X − v)` —
a monic `p`-polynomial, so `X^{p^ℓ} − L_V` has degree `≤ p^{ℓ−1} < k` — the challenge
`γ_V = −L_V(w)` is bad, with window `V ∪ {w}` (`isBad_subspacePencil`).  The graph family of
subspaces supplies `p^{ℓ(m−ℓ)}` distinct `V`, whose subspace polynomials are distinct
(`graphList_span_injective`, `subPoly_graph_injective`), and a pigeonhole choice of `w` makes
the challenges distinct (`exists_separating_point`).  Hence

```
#Bad ≥ p^{ℓ(m−ℓ)} ≈ n^{log_p(1/η)} .        (card_badSet_ge_twistLists, exists_subspacePencil)
```

**Asymptotic form** (`exists_superpolynomial_badSet_of_small_relative_gap`): for all `d, M`
there is `N` such that over every characteristic-`p` field with `p^N < |K|` there are a domain,
parameters with `|D| = k + e + c`, `1 ≤ c`, `M·c ≤ |D|` (so `η ≤ 1/M`), and a line with
`|D|^d < #Bad`.  So no polynomial bound on `#Bad` survives any hypothesis weaker than
`η = Ω(1)`, and the gap-layer law is refuted.

**The transition is exactly at constant gap.**  At `η = Ω(1)` this family gives only `n^{O(1)}`
— the exponent `ℓ(m−ℓ)/m ≈ log_p(1/η)` is bounded — so constant-gap Grand MCA is untouched.

**Why this family cannot be pushed** (`IndicatorLineList.lean`).  Its direction word is the
indicator of a single point.  For *any* such line,

```
#{distinct g(w) − f₀(w) : g ∈ rsList(k, e+1, f₀), g(w) ≠ f₀(w)}
    ≤ #Bad(f₀, 1_{\{w\}}) ≤ |rsList(k, e+1, f₀)|
```

(`image_rsList_sub_badSet_indicator`, `card_badSet_indicator_le_card_rsList`): the bad-set size
*is* a Reed–Solomon list size at radius `e+1`.  Producing a superpolynomial bad set at constant
`η` by an indicator line is therefore at least as hard as exhibiting an RS code with a
superpolynomial list at a constant gap to capacity, an open problem.  Any refutation of
constant-gap Grand MCA must use a direction supported on more than one point.

## 115. Arbitrary directions: `#Bad ≤ 1 + |D|·(list size of `f₁` at radius `2e`)`, and the pairwise barrier (`RequestProject/Root/CodingTheory/DirectionListReduction.lean`)

Write-up: `SUBSPACE_PENCIL_REPORT.md` §6b.

§114 bounded `#Bad` by a Reed–Solomon list size only for lines whose direction word is the
indicator of one domain point.  That restriction is now removed.  For **every** MCA line, with
no hypotheses at all (`card_badSet_le_mul_card_rsList`):

```
#Bad(k, e, f₀, f₁)  ≤  1 + |D| · #{ codewords of degree < k within distance 2e of f₁ } .
```

Mechanism.  Fix a bad `γ₀`, with window `S₀` and interpolant `P₀`.  For any other bad `γ`, with
window `S` and interpolant `P`, the degree-`<k` polynomial `Q_γ = (P − P₀)/(γ − γ₀)` agrees with
`f₁` on `S ∩ S₀`, a set of size `≥ |D| − 2e`; so `Q_γ` lies in the radius-`2e` list of the
*direction word*.  The fibre of `γ ↦ Q_γ` over a fixed `Q` has at most `|D|` elements
(`card_shiftFibre_le`): its members all share the codeword pair `(q₀, q₁) = (P₀ − γ₀·Q, Q)`, and
on the window each `γ` is determined by `γ·(f₁ − q₁)(x) = (q₀ − f₀)(x)` at any point where
`f₁ ≠ q₁`; such a point exists, since otherwise the whole line would be close on that window,
contradicting badness.

**Barrier** (`pairwise_route_within_unique_decoding`).  The radius produced is `2e`, not `e`.
The Johnson bound makes the radius-`2e` list polynomial precisely when the agreement `|D| − 2e`
exceeds `√(k·|D|)`; since `√(k·|D|) ≥ k`, that already forces `k + 2e < |D|`, the
unique-decoding regime.  So the correlated-pair route — of which the theorem above is the
sharpest list-theoretic form — can never certify a polynomial bad set beyond unique decoding,
however the "far" case is handled.  This explains formally why the near/far dichotomy of
`NearCodewordLineMCA.lean` stalls where it does, and it isolates what constant-gap Grand MCA
needs: an invariant of a *single* bad challenge (or of the bad set globally) rather than of
pairs.

## 116. Audit of the subspace-pencil asymptotics (`RequestProject/Root/CodingTheory/SubspacePencilAudit.lean`)

Full write-up: `CONSTANT_GAP_MCA_REPORT.md` §1.

`exists_superpolynomial_badSet_of_small_relative_gap` says: *for each* `(d, M)` there is a
parameter point with `η ≤ 1/M` and `#Bad > n^d`.  It does not say that every vanishing-gap
regime is superpolynomial, and that stronger reading is false for this family.  Four
elementary but certified facts delimit it (`2 ≤ p`, `1 ≤ ℓ ≤ m`, `n = p^m + 1`,
`k = p^{ℓ−1}+1`, `c = p^ℓ − p^{ℓ−1}`, guarantee `p^{ℓ(m−ℓ)}`):

| statement | content |
|---|---|
| `subspacePencil_bound_le_pow_card` | `p^{ℓ(m−ℓ)} ≤ n^{m−ℓ}`: the guarantee is polynomial at every fixed `η`, of degree `log_p(1/η)` |
| `subspacePencil_superpoly_forces_gap` | `n^d < p^{ℓ(m−ℓ)} → d < m − ℓ`: beating a bigger polynomial needs a smaller gap |
| `subspacePencil_gap_lt_of_superpoly` | the same as `p^d·c < n`, i.e. `η < p^{−d}` |
| `subspacePencil_vanishing_gap_linear_bound` | at `ℓ = 1`, `η ≤ p^{1−m} → 0` while the guarantee is `p^{m−1} < n`: a vanishing gap alone does **not** make the family superpolynomial |
| `subspacePencil_gap_eq_pred_mul` | `c = (p−1)(k−1)`: the family lives at vanishing *rate*, `η ≈ (p−1)ρ`, `δ → 1` |

Two further caveats: only the sparse grid `(n,k,c)` above is realised, with no transfer to
neighbouring parameters; and the construction needs `|F| > p^m + p^{2ℓ(m−ℓ)+ℓ}`, so the
certified `ε_mca ≥ #Bad/|F|` is below `p^{−ℓ(m−ℓ)}` — the result concerns `#Bad` versus
`poly(n)`, not the size of `ε_mca`.

## 117. Far centres: MCA *is* the proximity-gap problem (`RequestProject/Root/CodingTheory/FarCenterProximity.lean`, `RequestProject/Root/CodingTheory/SubspacePencilProximity.lean`)

Full write-up: `CONSTANT_GAP_MCA_REPORT.md` §2a.

`badSet ⊆ goodZ` always (`card_badSet_le_card_goodZ`), and

```
e < distToCode k f₀   →   badSet k e f₀ f₁ = goodZ k e f₀ f₁      (badSet_eq_goodZ_of_far)
```

because a window witnessing closeness of `f₀ + γ·f₁` would, if it carried the whole line,
carry its point at `γ = 0`, namely `f₀`.  Hence `grandMCA_iff_proximityGap`: for every bound
`B`, a uniform MCA bound for far-centred lines is *equivalent* to a uniform proximity gap for
them; and a proximity gap for all lines implies MCA for all lines
(`card_badSet_le_of_forall_card_goodZ_le`).  Constant-gap Grand MCA is therefore exactly the
constant-gap proximity-gap problem for Reed–Solomon lines.

The far-centre hypothesis is sharp: for `f₀, f₁` codewords, `goodZ = F` and `badSet = ∅`
(`goodZ_eq_univ_of_mem_code`, `badSet_eq_empty_of_mem_code`).  A general supply of far centres:
a polynomial word of degree `≥ k` is farther than `e` from the code once `deg + e < |D|`
(`lt_distToCode_of_le_degree`).  Applied to the subspace pencil, whose centre is `x ↦ x^{p^ℓ}`,
this gives `badSet_eq_goodZ_pencil` and hence the counterexample in proximity-gap form
(`exists_superpolynomial_goodZ_of_small_relative_gap`).

## 118. Near-direction lines: a single-challenge bad-set bound (`RequestProject/Root/CodingTheory/NearDirectionBadSet.lean`)

Full write-up: `CONSTANT_GAP_MCA_REPORT.md` §2b.

For every line and every codeword `q₁` of degree `< k`, with `t = d(f₁, q₁)`:

```
#Bad(k, e, f₀, f₁)  ≤  t · #{ codewords of degree < k within distance e + t of f₀ }
```

(`card_badSet_le_mul_card_rsList_direction`, no hypotheses).  A bad `γ` with window `S` and
interpolant `P` contributes the codeword `P − γ·q₁`, which agrees with `f₀` on
`S ∩ agree(f₁,q₁)` (`≥ |D| − e − t` points), together with a point `x ∈ S` where `f₁ ≠ q₁`
(one exists, else the whole line is close on `S`); and `γ·(f₁ − q₁)(x) = (P − γq₁ − f₀)(x)`
recovers `γ`.  Each bad challenge is charged **individually**, so this route is not subject to
the pairwise barrier of §115; at `t = 0` it gives `badSet = ∅`.

With the project's Johnson bound (`card_badSet_mul_le_of_near_direction`): if
`2|D|(k−1) ≤ a²` and `a ≤ |D| − e − t` then `#Bad · a ≤ 2t|D|`.  In relative terms
(`ρ = k/n`, `η = c/n`, `τ = t/n`) the bad set is polynomial whenever `ρ + η − τ > √ρ`, for an
arbitrarily far centre — a constant-gap MCA theorem for lines with a near-codeword direction,
strictly beyond unique decoding.

**The near-centre twin.**  Closeness on a window is invariant under scaling, and
`f₀ + γ·f₁ = γ·(f₁ + γ⁻¹·f₀)`, while line-closeness is symmetric in the two words
(`lineCloseOn_comm`).  So a nonzero bad challenge of `(f₀, f₁)` inverts to a bad challenge of
`(f₁, f₀)` (`isBad_swap`), the two bad sets differ by at most one element
(`card_badSet_le_succ_swap`), and the bound above has a mirror image
(`card_badSet_le_succ_mul_card_rsList_center`):

```
#Bad(k, e, f₀, f₁)  ≤  1 + d(f₀,q₀) · #{ codewords within distance e + d(f₀,q₀) of f₁ }
```

for every codeword `q₀`.  Hence a polynomial bad set is guaranteed as soon as **one** of the
two words of the line is near the code and the Johnson condition holds for the other; and a
line whose centre is a codeword has at most one bad challenge
(`card_badSet_le_one_of_center_mem_code`).

**Ceiling** (`nearDirection_ceiling_le_nearFar_ceiling`).  Splitting the general case on
`τ = d(f₁,C)/n` and handling `τ` large by the set-family Johnson bound (window intersections
are `≤ |D| − d(f₁,C)`) gives a dichotomy whose reach is `δ < (3 − √(5+4√ρ))/2`, never better
than the pair-split reach `δ < (3 − √(5+4ρ))/2` of `NearCodewordLineMCA.lean`, because the
Johnson step is applied to the centre and pays `√ρ` instead of `ρ`.  So the direction split
alone cannot improve the certified radius.

## 119. The triple-cluster proximity gap: `O(n)` close challenges below `δ = 1 − ρ^{1/3}` (`RequestProject/Root/CodingTheory/TripleEnergy.lean`, `RequestProject/Root/CodingTheory/TripleClusterProximity.lean`)

Full write-up in `TRIPLE_CLUSTER_REPORT.md`.  Write `n = |D|`, `ρ = k/n`, `δ = e/n`, and let
`HasCorrelatedAgreement k e f₀ f₁` mean that two codewords of degree `< k` agree with `f₀` and
`f₁` on one and the same window of at least `n − e` positions — the conclusion the
proximity-gap and MCA statements ask for.

**Main theorem** (`card_goodZ_mul_pow_three_le`).  For *every* line, if the line has no
correlated agreement at radius `e`, then the number `N` of `e`-close challenges satisfies

```
N · (n − e)³  ≤  N · (k−1) · n²  +  (e+2) · n³ .
```

Hence (`card_goodZ_le_of_gap`) `N · c ≤ (e+2)·n` whenever `(k−1)n² + c·n² ≤ (n−e)³`, so at a
constant relative gap in `(1−δ)³ > ρ` the close set is `O(n)`.  For a **far centre**
(`e < d(f₀,C)`) correlated agreement is impossible and, by
`FarCenterProximity.badSet_eq_goodZ_of_far`, the MCA bad set equals the close set:
`card_badSet_le_of_far_of_gap` gives `#Bad · c ≤ (e+2)·n` and `epsMCA_le_of_far_of_gap` gives
`ε_mca ≤ (e+2)n/(c|F|)`, with **no hypothesis at all on the direction** `f₁`.  This is the
far–far regime.  `card_badSet_le_of_far_of_rate_radius` is the fully explicit form: at
`k ≤ 3n/10` and `e ≤ 3n/10`, `#Bad ≤ 25(e+2) = O(n)`.

**Radius.**  The hypothesis is `(k−1)n² < (n−e)³`, i.e. `δ < 1 − ρ^{1/3}`.
`gap_of_three_mul_lt` certifies that `3e < n − k + 1` implies it, so the regime strictly
contains the unique-decoding row of §-`MCA.lean`; it also contains the pair-split ceiling
`δ < (3 − √(5+4ρ))/2`, which solves `(1−δ)² > ρ + δ`.  At `ρ = 1/4` the certified radius moves
from `0.25`/`0.275` to `0.370` (Johnson would be `0.5`).  `regime_example_1000_251_300`
certifies a concrete point in the new regime and outside the old one.

**Mechanism** (why this is not a pairwise argument).  A pair of close challenges gives only a
`n − 2e` window.  Instead: (i) a *triple* whose agreement sets meet in `≥ k` positions forces
the polynomial identity `p₃ = q₀ + γ₃·q₁` (`eq_add_smul_of_card_inter_ge`), because a
polynomial of degree `< k` with `k` roots vanishes; (ii) `e+2` challenges sharing one affine
pair force correlated agreement on a **full** `n − e` window (`card_cluster_le`), the sets
`A_γ \ T` being pairwise disjoint; (iii) therefore, without correlated agreement, every
ordered pair has at most `e+1` such partners, and the third-moment identity
`∑ₓ mult(x)³ = ∑_{γ₁γ₂γ₃} |A_{γ₁} ∩ A_{γ₂} ∩ A_{γ₃}|` together with Jensen
`(∑ₓ mult x)³ ≤ n²∑ₓ mult(x)³` (`TripleEnergy.card_mul_pow_three_le`) bounds `N`.  The
invariant is global: triples are constrained, the cardinality of the whole close set is
bounded.

**Consistency.**  The superpolynomial subspace pencil of §114 needs `ℓ < m`, while the new
hypothesis needs `ℓ ≥ m`: the counterexample family lies exactly outside the certified regime
(as it does outside the Johnson regime).  The band `1 − ρ^{1/3} ≤ δ < 1 − ρ` remains open.

**Pair-energy companion** (`card_goodZ_pair_dichotomy`, `card_goodZ_le_of_pair_gap`,
`card_badSet_le_of_far_of_pair_gap`).  The cluster step also sharpens the second moment:
without correlated agreement, either `N ≤ e+1` or every pairwise intersection is `< k+e`
(a pair meeting in `k+e` positions sweeps the whole line into one cluster), whence
`N·(n−e)² ≤ N·(k+e−1)n + n²` and `N ≤ max(e+1, n/c)` in the regime `(n−e)² > (k+e−1)n`,
i.e. exactly the pair-split ceiling `δ < (3−√(5+4ρ))/2`, which the cubic regime contains.

## 120. Witness elimination for far-centred lines (`RequestProject/Root/CodingTheory/WitnessElimination.lean`)

The algebraic half of the far-centred proximity problem, in three unconditional pieces.  Full
discussion, including the exact remaining gap, in `WITNESS_ELIMINATION_REPORT.md`.

**Elimination** (`card_le_natDegree_of_yfree_combination`).  Work in `F[Z][X][Y]`; let
`subst γ p` be the substitution `Z ↦ γ, Y ↦ p`.  If `C R = U·Q₁ + V·Q₂` with `R ∈ F[Z][X]`,
and every challenge `γ` of a finite set `G` has a witness `p_γ` with
`subst γ p_γ Q₁ = subst γ p_γ Q₂ = 0`, then every `X`-coefficient of `R` vanishes on `G`, so
`#G ≤ deg_Z (R.coeff j)` for any `j` with `R.coeff j ≠ 0`.  This is the exact, hypothesis-free
"eliminate the challenge" step: no genericity, no field-size and no radius condition, and no
resultant machinery — any explicit `Y`-free element of the ideal serves.

**Incidence count** (`card_mul_le_of_lineResidual`).  For `W ∈ F[Z][X][Y]` the *line residual*
at `x ∈ D` is `Z ↦ W(Z, x, f₀ x + Z·f₁ x) ∈ F[Z]`, of degree `≤ deg_Z W + deg_Y W`
(`natDegree_lineResidual_le`).  If all residuals have degree `≤ d`, the positions where the
residual vanishes identically number `≤ n − e − s`, and each `γ ∈ G` has a witness killing `W`
and agreeing with the line on `≥ n − e` positions, then `#G · s ≤ n · d`.  The formalisation
also makes precise why this cannot be applied to a Guruswami–Sudan interpolant itself:
interpolating the line points with multiplicity `≥ 1` makes *every* line residual vanish, so
the count is only usable on a proper factor.

**Polynomial witness families over a far centre** (`card_le_of_polynomial_witness_family`).
For `P ∈ (F[X])[Z]` with `deg P₀ < k` and a centre with `e < d(f₀, RS[D,k])`, at most
`n · max (deg_Z P) 1` challenges are `e`-close with witness `P(γ,·)`.  Here the far centre is
what pays: the residual `Z ↦ P(Z,x) − f₀ x − Z f₁ x` vanishes identically exactly where
`f₀ x = P₀(x)`, and `≥ n − e` such positions would make `f₀` itself `e`-close.  Corollaries for
`goodZ` and `badSet`, and the union form `card_goodZ_le_of_witness_families`:
`t` families of `Z`-degree `≤ d` give `#goodZ ≤ t·n·max d 1`.

**Status.**  These are the two ends of the Guruswami–Sudan chain over `F[Z]`; the branch that
remains open is a common irreducible factor of the interpolation module of small `Y`-degree
(a *rational* witness family, or an irreducible factor of `Y`-degree `≥ 2`).  The report
records a dimension count showing that a common factor of large `Y`-degree is impossible, so
the open branch is confined to small `Y`-degree.  No new certified radius is claimed.

**Scaled (rational) witness families** (`card_le_of_scaled_polynomial_witness_family`,
`card_goodZ_le_of_scaled_witness_family`).  The `Y`-degree-one factor of a Guruswami–Sudan
interpolant gives witnesses that are polynomial only up to a scalar depending on the
challenge, `p_γ = a(γ)⁻¹·B(γ,·)` with `a ∈ F[Z]`.  Over a far centre this case is bounded
too: at most `n·max(deg_Z B, deg a + 1)` challenges are `e`-close with such a witness, and
`#goodZ ≤ deg a + n·max(deg_Z B, deg a + 1)` if every other close challenge is a root of `a`.
The far-centre kill now happens at the *trailing* coefficient of `a`: an identically
vanishing residual `B(Z,x) − a(Z)·(f₀ x + Z f₁ x)` gives `f₀ x = (a_{ord a})⁻¹·B_{ord a}(x)`.

**Dichotomy form** (`card_le_or_lineSupport_large`).  For any trivariate `W` killed by the
witness of every challenge of `G` and with line residuals of degree `≤ d`: either
`#G ≤ n·d`, or `W` vanishes identically along the line at all but at most `e` positions.
The second alternative is exactly the degenerate branch that the far-centre hypothesis has to
eliminate, and it is eliminated in the polynomial and scaled-polynomial family cases above.

## 121. Closing the irreducible-carrier branch: affine carriers, sharp carrier budget, and the deployed-target gap (`RequestProject/Root/CodingTheory/AffineCarrier.lean`, `RequestProject/Root/CodingTheory/CarrierBudget.lean`, `RequestProject/Root/CodingTheory/DeployedTargetGap.lean`)

Full write-up in `AFFINE_CARRIER_CLOSURE.md`.

**Affine carriers.** `IsAffineCarrier k W` is the published BCHKS/BCI+20 conclusion for a
"useful" irreducible factor: `W = c·(Y − v₀(X) − Z·v₁(X))` with `c ≠ 0` and
`deg v₀, deg v₁ < k`. For such a `W` the line residual at a position `x` is the linear
polynomial `c·((f₀x − v₀(x)) + (f₁x − v₁(x))·Z)`, so

* `mem_lineSupport_iff_of_affineCarrier`: `x ∈ lineSupport W ↔ f₀x = v₀(x) ∧ f₁x = v₁(x)` —
  degeneracy of an affine carrier *is* correlated agreement;
* `isFormalRoot_of_affineCarrier`, `lineCloseOn_of_affineCarrier`,
  `correlatedAgreement_of_degenerate_affineCarrier`: it yields a formal root of `Z`-degree
  `≤ 1` on that set, hence correlated agreement at radius `e + 1`;
* `not_degenerate_of_affineCarrier_of_far`: over a centre at distance `> e + 1` from the code
  an affine carrier cannot be degenerate;
* `card_badSet_le_of_affine_carriers`: hence the last branch of the carrier dichotomy is
  closed, `#Bad ≤ dZ + L·|D|·(dZ + L)`, under the explicit hypothesis that every degenerate
  irreducible carrier is affine. That hypothesis is exactly the published Hensel-lifting step
  and is **not** reproved here.

**Sharp carrier budget.** Degrees are additive over a factorisation, so charging the global
budget once per factor is a spurious `deg_Y Q` loss. `zDeg` (total `Z`-degree, through
`F[Z][X][Y] ≅ F[X][Y][Z]`), `zDegLe_iff`, `zDeg_multiset_prod` and
`card_le_of_factorisation_budget` give the per-factor accounting, and
`card_le_or_exists_degenerate_irreducible_sharp` improves the dichotomy bound from
`dZ + L·|D|·(dZ + L)` to `dZ + |D|·(dZ + L)`; `card_badSet_le_of_affine_carriers_sharp` is the
closed branch in that sharp form.

**The deployed target.** `deployedRate = 1/2`, `deployedRadius = 0.46782684`:
`deployedRadius_lt_capacity` (capacity gap `0.03217316`),
`deployedRadius_beyond_johnson` (`(1−δ)² < ρ`), `johnson_slack` (the Johnson inequality fails
by a factor `> 1.76`) and `gs_condition_fails` (the project's Guruswami–Sudan condition
`k·n·(m+1) < m·t²` is false there for *every* multiplicity `m` and every block length). So no
Johnson-type argument — the carrier route included — reaches that row.

Caveats, restated: the carrier chain still lacks an existence theorem for the formal-line
interpolant with explicit `(L, dZ)`, so it yields no numerical bad-set bound yet; and by the
accounting of `KOALAIRS12_PRIZE_GAP_AUDIT.md` the MCA constant is worth `0` bits at the audited
parameter shape, only the radius is.

## 122. The prefix/image fibre of the deployed Mersenne boundary-prefix atom, and the exact max/average constant (`RequestProject/PrefixFibre.lean`)

Objects (see `PREFIX_FIBRE_ATOM_REPORT.md` for the reading of the question): over the Mersenne
field `2^s − 1`, the *boundary-prefix atom* `atom m = {0,…,2^m−1}`, the `b`-bit image prefix
`prefixBits s b y = y/2^(s−b)`, the deployed *primitive free twiddle* `twiddle s k x = 2^k·x
mod (2^s−1)` and the *prefix/image fibre* `fibre s m b k j`.  The average fibre size is
`2^m/2^b`; all bounds are in the denominator-free form `card·2^b ≤ C·2^m`.

**Exact, row-sharp law on the coherent branch** (`k + m ≤ s`, `k + b ≤ s`).
`card_fibre_coherent` gives the exact count of every fibre, `card_fibre_zero` the largest one
(`2^min(s−k−b, m)`, at bucket `0`) and `card_fibre_mul_le` / `card_fibre_zero_mul` the
max/average law in its sharp form

  max fibre `=` `2 ^ min (s − k − m) b` `×` average,

an identity, not an estimate: the factor is exactly `2^t` for the boundary overhang
`t = s − k − m`, capped by the prefix width.

**The other branches.**  `card_fibre_periodic`: if `s ≤ k + m` (and `k + b ≤ s`) the twiddle
folds the atom, the fibre map is `2^(s−k)`-periodic and every bucket gets exactly the average
— factor `1`.  `card_fibre_wrapped_le_one` / `card_fibre_wrapped_ratio`: if `m + k ≤ s ≤ k + b`
the fibres are singletons and the factor is exactly `2^(b−m)`.  (The doubly-wrapped corner
`s ≤ k + m` *and* `s ≤ k + b` is not formalised; it lies inside the periodic branch.)

**The constant `9.57219783037`.**  `target_between`: `8 < 9.57219783037 < 16`, and the sharp
factor only takes powers of two.  Hence `target_holds_of_overhang_le_three` (bound holds, with
sharp constant `8`, whenever `s ≤ k+m+3`), `target_fails_deployed` and
`deployed_ratio_eq_sixteen` (at `s=31, m=20, b=8, k=7` the ratio is exactly `16`, so the bound
is false — an explicit counterexample), and the exact criterion `target_holds_iff`: for
`b ≥ 4`, the bound holds for every bucket **iff** `s ≤ k + m + 3`.
`sharp_constant_deployed`: at `m = 20`, `b = 8` the exact factor is `2^min(11−k,8)`, so the
uniform sharp constant over all `31` free twiddles is `256`.

**Why this is Mersenne.**  `twiddle_eq_rotate`: for `x < 2^s−1`, multiplication by `2^k` is the
cyclic rotation of the `s`-bit word, so image prefixes are bit windows and every fibre count is
a power of two.  `koalabear_no_rotation`: for `2^31 − 2^24 + 1` no `2^k`, `1 ≤ k ≤ 31`, is `1`,
so no word length makes the deployed twiddles rotate and the exact law does not transfer.

Pre-verified by `analysis/prefix_fibre_atom_measure.py` (exhaustive over `s = 5, 7, 13`, all
`m, b, k`; 0 mismatches) and cross-checked against the Lean definitions by `#eval`.

---

## 25. Grand MCA — the seven-witness certificate at `RS[F_17^32, μ_512, 256]`

`RequestProject/Root/CodingTheory/GrandMCASevenWitness.lean` (no `sorry`; axioms `propext`,
`Classical.choice`, `Quot.sound`).

For `K = F_{17^32}`, `H = μ_512 ⊆ K^*` (`512 = 2^9`, and `v₂(17^32 − 1) = 9`), `C = RS_256(H)`,
radius `e = 250` (`δ = 125/256`, closed agreement threshold `262`), the single pencil

  `f₀(x) = x^264`,   `f₁(x) = x^256`

has at least seven officially bad challenges, namely
`γ_t = −(Σ_{i<32} θ^{8i} + θ^{256+8t})`, each witnessed by the union `S_t` of `33` of the `64`
`μ_8`-cosets of `H` (`|S_t| = 264 ≥ 263 > 262`).  Since `⌊17^32 / 2^128⌋ = 6`, seven witnesses
already give

  `ε_mca ≥ 7/17^32 > 2^{-128}`   (`epsMCA_gt_two_pow_neg_128`, `exists_grandMCA_seven_witness`).

Key declarations: `mulDomain` / `mulCoset` and their binomial vanishing polynomials over an
arbitrary field (generalising the `ZMod p` coset domains of `CapacityGapCosets`),
`isBad_of_radius_le`, `card_image_le_card_badSet_blocks`, `GrandMCASeven.isBad_wit`,
`GrandMCASeven.official_event`, `GrandMCASeven.card_gammas`,
`GrandMCASeven.seven_le_card_badSet`.  Full discussion, including the scope of the claim and
the paused `c = 2` Plücker route, in `GRAND_MCA_SEVEN_WITNESS_REPORT.md`.

---

## 26. Grand MCA — an **exact** row: `RS[F_q, μ_512, 256]` with `q = 5·2^127 + 1`

`RequestProject/Root/CodingTheory/ProthPrimeCertificate.lean` and
`RequestProject/Root/CodingTheory/GrandMCAExactThreshold.lean` (no `sorry`; axioms `propext`,
`Classical.choice`, `Quot.sound`; no `native_decide`).

Field: `q = 5·2^127 + 1 = 850705917302346158658436518579420528641` is **prime**
(`Root.NumberTheory.qProth_prime`), certified by the Lucas test with base `17` through an
explicit chain of `127` repeated squarings.  (The Proth witness `3` is *not* usable for the
Lucas test: `3^{(q−1)/5} ≡ 1`, so `3` has order `2^127`.)  Here `q − 1 = 5·2^127`, so
`H = μ_512` exists (`dom_eq_nthRootsFinset`), and `2^129 < q < 3·2^128`, so `⌊q/2^128⌋ = 2`.

| side | statement | Lean name |
| --- | --- | --- |
| safe | every line has `#Bad ≤ 2` and `ε_mca < 2^{-128}` at every radius `e ≤ 1` | `ExactRow.epsMCA_le_of_radius_le_one`, `ExactRow.epsMCAmax_le_of_radius_le_one` |
| unsafe | the triangle line `f₀ = 2·1_a + 1_b`, `f₁ = −1_a − 1_b + 1_c` has the three bad challenges `0,1,2` at `e = 2` (`δ = 1/256`), so `ε_mca ≥ 3/q > 2^{-128}` | `ExactRow.epsMCA_two_gt`, `ExactRow.epsMCA_gt_of_two_le` |
| exact | `#Bad = 3` at `e = 2`; the critical integer radius is `e_crit = 2` | `ExactRow.card_badSet_eq_three`, `ExactRow.exists_exact_grandMCA_row` |
| endpoint | the safe real radii are exactly `[0, 1/256)`; supremum `δ* = 1/256` is **not attained** | `ExactRow.safeRadii_eq`, `ExactRow.isLUB_safeRadii`, `ExactRow.one_div_256_notMem_safeRadii` |

The unsafe mechanism is general (any field with `char ≠ 2`, any domain with `k + 3 ≤ |D|`):
`not_isCloseOn_oneHot`, `isBad_of_oneHot_witness`, `triangle_isBad_zero/one/two`,
`three_le_card_badSet_triangle`, and `card_badSet_triangle_eq_three`, the last showing that
the `#Bad ≤ e + 1` cap of `BadSetPencilBound.card_badSet_le_succ_radius_of_le` is **sharp at
`e = 2`**.  Discussion, scope and prior-work audit: `GRAND_MCA_EXACT_THRESHOLD_REPORT.md`.

## 27. Subfield descent: the base-field-rational class is dead on the deployed Grand-MCA row

`RequestProject/Root/CodingTheory/SubfieldDescent.lean`,
`RequestProject/Root/CodingTheory/KoalaBearRowDescent.lean` (both `sorry`-free; axioms
`propext`, `Classical.choice`, `Quot.sound`).

**Descent lemma.** If a ring endomorphism `σ` of the code field fixes the evaluation domain
pointwise and fixes both words of the pencil, then every officially bad challenge is fixed by
`σ` (`isBad_fixed_of_ringHom`).  Consequently a pencil rational over a subfield of size `q`
has `#Bad ≤ q`, and a pencil merely *spanning* a base-field-rational plane has `#Bad ≤ p+1`.

**Deployed row** (`p = 2^31−2^24+1` proved prime, `F = F_{p^6}`, `H = μ_{2^21} ⊆ F_p`,
`k = 2^20`, rate 1/2, `B* = ⌊|F|/2^128⌋ = 274980728111395087`): for **every** radius and every
base-field-rational pencil, `#Bad ≤ p < 2^31`, i.e. `#Bad < B*` by 27 bits, and
`ε_mca ≤ p^{-5} < 2^{-154.9} ≪ 2^{-128}`.  This removes the entire class — power pencils,
coset-union/graded/HalfGap constructions, one-hot triangles — from the whole
Johnson→capacity corridor of that row.  For proper subfields: an `F_{p^2}`-rational
counterexample would need more than `1/17` of `F_{p^2}` to be bad, an `F_{p^3}`-rational one
more than a `2^{-36}` fraction of `F_{p^3}`.

Exact measurements (`analysis/subfield_descent_check.py`,
`analysis/challenge_image_entropy.py`) confirm the cap is tight (base-field pencils attain
exactly `q` challenges) and locate the escape route (extension coefficients at degree `≥ k+2`,
where the challenge map sees two independent `F_p`-coordinates of the support data).
Full write-up: `GRAND_MCA_SUBFIELD_DESCENT_REPORT.md`.

## 28. The general invariant form of MCA: any linear code, any zero-evading generator

`RequestProject/Root/CodingTheory/GeneralMCAInvariant.lean`, `GeneralMCAInstances.lean`,
`GeneralMCAReedMuller.lean`, `GeneralMCAWindowSharp.lean`.

Mutual correlated agreement in the unique-decoding-type window depends on exactly three
numbers: the separation `σ` of the code (`σ = N − d`), the zero-evading number `B` of the
generator curve `γ ↦ (g γ j)_{j<ℓ}` (the maximal number of challenges of `Γ` on a hyperplane of
`F^ℓ`), and the length `N = |Ω|`.

* `card_badSetAbs_le_of_zeroEvading` : `σ + (B+2)e < N ⟹ #Bad ≤ B(e+1)`, for an arbitrary
  linear code `C ⊆ (Ω → F)`, an arbitrary challenge alphabet `Γ ⊆ F` and an arbitrary
  zero-evading generator. `card_badSetAbs_le` is the arc form `σ + (ℓ+1)e < N ⟹
  #Bad ≤ max(ℓ−1, B(e+1))`, and `allCloseOn_of_card_close_gt` the correlated-agreement form.
  The bound is independent of `|F|`.
* `interp_of_card_gt` : the arc principle — more than `B` challenges of a zero-evading
  generator span `F^ℓ`, so interpolation is not an extra hypothesis.
* Generator instances: `zeroEvading_pow` (power generator, `B = ℓ−1`), `zeroEvading_monomial`
  (distinct exponents), `zeroEvading_polyGen` (any polynomial generator with independent
  components of degree `≤ B`), `zeroEvading_cauchy` (the **rational** generator
  `1/(γ − a_j)`, which is not polynomial, `B = ℓ−1`).
* Code instances: `separated_of_minDistance` (any linear code), `separated_rsCode`
  (`σ = k−1`), `card_badSetAbs_evaluation_le` (any evaluation code with a zero bound — for
  `C_L(G)` on a curve this is `σ = deg G`), `separated_rmCode` / `card_badSetAbs_rm_le`
  (Reed–Muller on the grid `S^n`, `σ = d·|S|^{n−1}`, via Mathlib's Schwartz–Zippel).
* Alphabet generality: the symbol alphabet of the code is an arbitrary `F`-vector space, so
  folded codes are covered — `separated_foldCode` (folding by blocks of size `s` divides the
  separation by `s`) and `card_badSetAbs_folded_le`.
* `card_badSetG_le_via_general` recovers the concrete Reed–Solomon polynomial-generator bound
  of section 21 from the abstract theorem.
* Exactness: `exists_card_badSetAbs_eq_sharp` — the bound `B(e+1)` is attained;
  `exists_badSetAbs_ge_at_window_boundary` — at `σ + (ℓ+1)e = N` the bad set is unbounded, so
  the window is optimal. Together these close the invariant-level question and show that any
  progress beyond the unique-decoding frontier must use structure invisible to `(σ, B, N)`.

Novelty gate and scope: `GENERAL_MCA_INVARIANT_REPORT.md`.

## 29. The spread-weighted incidence reduction: eliminating the challenge coordinate (`RequestProject/Root/CodingTheory/SpreadIncidence.lean`)

The incidence set of official badness witnesses,
`I_e = {(γ,S,q) : |S| ≥ N−e, (f₀+γf₁)|_S = q|_S, ¬LineCloseOn S f₀ f₁}`, is analysed through
its projection to the challenge coordinate. Every witness is attached to a pair of codewords
`(c₀,c₁)`, and the fibre over such a pair is controlled by the **deviation-active set**
`A = devActive f₀ f₁ c₀ c₁ = {x ∈ D : f₀ x ≠ c₀ x or f₁ x ≠ c₁ x}`.

* `card_badWithPair_le_card_devActive` and `card_badWithPair_mul_sub_le`: `m ≤ |A|` and the
  spread inequality `m·(|A| − e) ≤ |A|`; hence `card_badWithPair_le_spreadWeight`
  (`m ≤ spreadWeight e |A|`) and `card_badWithPair_le_succ_radius` (`m ≤ e+1`)
  **unconditionally** — no window, no radius bound, no field-size condition.
* `card_badSet_le_sum_spreadWeight`: the reduction
  `#Bad ≤ max 1 (Σ_{p ∈ bigPairs} spreadWeight e |A_p|)`, and the coarse corollary
  `#Bad ≤ max 1 ((e+1)·#bigPairs)` per line. The challenge coordinate is gone; what remains
  is a spread-weighted count of codeword pairs jointly close to the line, i.e. data of the
  evaluation domain.
* `card_devActive_le_two_mul_of_two_le`, `mul_pred_card_devActive_le`: a pair explaining `m`
  challenges has joint deviation `|A| ≤ m·e/(m−1) ≤ 2e`; the extremal multiplicity `e+1`
  forces `|A| ≤ e+1`, so the heavy pairs live at joint radius `≈ e`, not `2e`.
* `card_badSet_le_two_scale`: only concentrated pairs pay the full price `e+1`; a pair with
  deviation spread `≥ 2e` pays `2`.
* `card_devActive_add_ge_of_ne`, `mul_pred_card_le_of_two_pairs`: two distinct pairs cannot
  both be concentrated (`N ≤ |A| + |A′| + k − 1`), which for equal multiplicities gives
  `(m−1)(N−k+1) ≤ 2me` — a fibre bound valid in the whole unique-decoding range `2e < N−k+1`.
* `HoleWitness.two_le_card_rsBigPairs_hole`
  (`RequestProject/Root/CodingTheory/SpreadIncidenceWitness.lean`): on the smallest known
  failure row (`|D| = 8 ⊆ F₁₃`, `k = 3`, `e = 2`, four bad challenges) the pair invariant is
  `≥ 2` — the excess over `e+1` is caused by a second codeword pair, not by the challenge.

Scope, novelty gate and the isolated remaining domain question: `SPREAD_INCIDENCE_REPORT.md`.

## 30. The weighted interleaved list profile: MCA as a layer cake, and the deployed pivot `m = 16` (`RequestProject/Root/CodingTheory/WeightedInterleavedList.lean`, `DeployedWeightedList.lean`)

The spread-weighted reduction of §29 is refined into a **layer-cake reduction against the
interleaved (pair) list profile** of the Reed–Solomon code,

`L₂(r) = #{(c₀,c₁) ∈ RS_k(D)² : |{x : f₀x ≠ c₀x ∨ f₁x ≠ c₁x}| ≤ r}` (`pairListProfile`),

with the multiplicity radius `pairRadius e m = ⌊m·e/(m−1)⌋` (`= 2e` for `m ≤ 1`).

* `card_badSet_le_sum_pairListProfile`: `#Bad ≤ max 1 (Σ_{m=1}^{e+1} L₂(pairRadius e m))` —
  the challenge coordinate is replaced by a sum of interleaved list sizes at *decreasing*
  radii; the coarse `#Bad ≤ (e+1)·#bigPairs` is this sum with every layer replaced by its
  largest term.
* `card_badSet_le_heavy_light`, `card_badSet_le_of_no_heavy`: multiplicity stratification at
  an arbitrary threshold `M`, `#Bad ≤ max 1 ((M−1)·L₂(2e) + (e+2−M)·L₂(r))`.
* `card_pairListProfile_mul_choose_le` (abundance bridge): `L₂(r)·C(|D|−r,k) ≤ C(|D|,k)`, the
  MDS `k`-subset double count transported from challenges to codeword pairs, via the pair
  agreement bound `card_jointAgree_inter_le`; non-vacuous iff `r + k ≤ |D|`
  (`pos_choose_sub_iff`).
* Deployed row (`n = 2^21`, `k = 2^20`, `δ = 61319/131072`, `e = 981104`,
  `B* = 274980728111395087`): `pairRadius_le_iff_sixteen_le` — for `m ≥ 2` the pair radius
  drops below `n − k = n/2` **exactly at `m = 16`** (`m = 15 : 1051182`, `m = 16 : 1046510`);
  `abundance_visible_iff_sixteen_le` — the abundance bridge becomes non-vacuous at the *same*
  `m = 16`, so heavy = abundance-visible and light = abundance-blind
  (`deployed_light_abundance_vacuous`: `C(n−2e,k) = 0`).
* Deployed gates: `deployed_heavy_light`
  (`#Bad ≤ max 1 (15·L₂(2e) + 981090·L₂(1046510))`), `deployed_dichotomy_prize`
  (`#Bad > B*` ⇒ a heavy pair, or `L₂(2e) ≥ 1.83·10^16`), `deployed_dichotomy_orbit`
  (`#Bad ≥ 2^59+1` ⇒ a heavy pair, or `L₂(2e) ≥ 3.84·10^16`), and the coarse pair gates
  `deployed_bigPairs_ge_prize` (`≥ 2.80·10^11` big pairs) and `deployed_bigPairs_ge_orbit`
  (`≥ 5.88·10^11`).
* Barrier: `heavy_agreement_sq_lt_johnson(')` — even the heavy sector has guaranteed
  agreement `1050642` with `1050642² < n·k`, strictly below the Johnson agreement `√(n·k)`,
  so no Johnson/Fisher pairwise count closes it. No post-Johnson advance is claimed.

Full discussion, novelty gate and the assessment of the pair-code generalized weights
`d_r(C²) = N − k + ⌈r/2⌉` (correct, but `d_2 = d_1`, hence no usable consequence):
`WEIGHTED_INTERLEAVED_LIST_REPORT.md`.

## 31. Field reduction: the multiplication algebra as a Desarguesian spread, and the exact six-coordinate normal form (`RequestProject/Root/CodingTheory/DesarguesianSpread.lean`, `SpreadMCA.lean`, `FieldReductionNormalForm.lean`, `SpreadIncidenceBarrier.lean`, `KoalaBearFieldReduction.lean`)

* **Spread set.** `mulLeft_sub_bijective`: for `r ≠ s` the difference `ρ(r) − ρ(s) = ρ(r−s)`
  of the regular representation of `K/F` is invertible. The graphs `spreadElem r = {(v,r·v)}`
  plus `spreadInf = {0}×K` form the field-reduction spread `spreadMember : Option K →
  Submodule F (K × K)`: distinct members meet in `0` (`spreadMember_inter_eq_bot`), every
  nonzero vector lies on exactly one (`existsUnique_spreadMember`, slope map `spreadIndex`),
  each member has `F`-dimension `[K:F]` (`finrank_spreadElem`, `finrank_spreadInf`), and the
  family is invariant under `K`-scaling and projective inversion.
* **MCA = spread incidence.** With `devVec x = (f₁x−c₁x, f₀x−c₀x)`:
  `mem_pairAgree_iff_devVec_mem_spreadElem` (agreement at `x` for `γ` ⟺ `devVec x` lies on the
  member `−γ`), `spreadIndex_devVec`, `badWithPair_subset_image_challengeAt` (every explained
  challenge is the slope of a deviation vector), `card_badWithPair_le_card_devActive'`, and
  the exact fibre description `mem_badWithPair_iff_votes` + `mem_votes_iff`.
* **Rank (linear-set) theorem.** `card_badWithPair_le_of_finrank`:
  `(|F|−1)·m + 1 ≤ |F|^{dim_F W}` when the deviation locus lies in `W ⊆ K × K`; rank one gives
  `m ≤ 1` (`card_badWithPair_le_one_of_finrank_le_one`), and globally
  `card_badSet_le_card_bigPairs_of_rank_one`.
* **Exact normal form.** `repr_lineComb` (the line is `U + M(γ)·V` in coordinates) and
  `isCloseOn_iff_forall_coord` / `lineCloseOn_iff_coord` / `isBad_iff_coord`: for a domain
  inside the base field, official `K`-valued MCA is the interleaved base-field problem on one
  **common support**, correlated clause preserved.
* **Deployed row** (KoalaBear `p = 2^31−2^24+1`, `K = F_{p^6}`, `H = μ_{2^21}`, `k = 2^20`):
  `secKB_spec`, `isBad_iff_coord_deployed`, `mem_badSet_iff_coord_deployed` (six-coordinate
  common-support form), `card_badWithPair_rank_bound_deployed`,
  `heavy_pair_rank_ge_two_deployed` (any pair explaining ≥ 2 challenges has `F_p`-rank ≥ 2).
* **Barrier.** `exists_spread_configuration`: whenever `m·(a−e) ≤ a` a spread configuration
  with `m` challenges and `a` vectors exists, so `m·(|A|−e) ≤ |A|` is the complete content of
  the field-reduction picture; no further quantitative gain comes from the spread alone.

Write-up: `FIELD_REDUCTION_SPREAD_REPORT.md`. Axioms audited in
`RequestProject/FieldReductionAxiomAudit.lean`. Grand MCA is not resolved; the deployed
UNSAFE certificate is used as given, not re-proved.

## 32. The Frobenius-orbit budget: Galois-type constraint-rank compression is capped at `p + 1` challenges (`RequestProject/Root/CodingTheory/SemilinearPlaneDescent.lean`, `SemilinearPlaneClassification.lean`, `FrobeniusOrbitBudget.lean`, `KoalaBearSemilinearRow.lean`, `KoalaBearOrbitDimension.lean`)

* **Semilinear descent.** `isBad_semilinear_rel`: if a ring endomorphism `σ` fixes the domain
  pointwise and maps the pencil into the plane it spans *modulo the code*
  (`σf₀ = a f₀ + b f₁ + g₀`, `σf₁ = c f₀ + d f₁ + g₁`, `deg gᵢ < k`), then every officially bad
  challenge satisfies `b + d·σγ = γ·(a + c·σγ)`. For `σ y = y^q` this is a nonzero degree-`≤ q+1`
  equation, so `card_badSet_le_of_semilinear`: `#Bad ≤ q + 1` at every rate and radius. The class
  is closed under scaling by any constant of the big field and under codeword shifts
  (`card_badSet_le_of_scaled_baseField`), unlike the fixed-value descent of `SubfieldDescent.lean`.
* **Speiser / Galois descent.** `span_fixed_of_stable`: a `K`-subspace of a function space stable
  under the coordinatewise action of `σ` is spanned by its `σ`-fixed vectors (averaging + Artin
  independence of characters). Hence `KoalaRow.frobenius_stable_plane_is_baseField`: a
  Frobenius-stable pencil plane is spanned by base-field-valued words.
* **The general budget.** `exists_orbit_annihilator` and `card_badSet_mul_le_of_orbit`: with no
  hypothesis on the pencil, writing it in a basis of `d` `σ`-fixed words spanning its Frobenius
  orbit, every bad challenge produces a nonzero `σ`-fixed covector annihilating `a + γ b`, and
  distinct bad challenges produce non-proportional covectors, so
  `#Bad · (q − 1) + 1 ≤ q^d` with `q = #Fix(σ)`, i.e. `#Bad ≤ 1 + q + ⋯ + q^{d−1}`.
* **Deployed row** (KoalaBear `p = 2^31−2^24+1`, `K = F_{p^6}`, `H = μ_{2^21}`, `k = 2^20`):
  `KoalaRow.card_fix_frobenius` (`#Fix = p`), `KoalaRow.card_badSet_orbit_bound`
  (`#Bad·(p−1)+1 ≤ p^d`), `KoalaRow.koalaRow_semiInvariant_safe` (Frobenius-stable-mod-code
  pencils are safe at every radius, `ε_mca < 2^{−154.9}`), `KoalaRow.semilinear_frontier`
  (`p + 1 < B* < p² + 1`), and the audit gate
  `KoalaRow.prizeBreaking_orbit_dim_ge_three`: **a pencil breaking the Prize challenge threshold
  must have Frobenius-orbit dimension `d ≥ 3`.**

Write-up: `FROBENIUS_ORBIT_BUDGET_REPORT.md`. Axioms audited in
`RequestProject/SemilinearDescentAxiomAudit.lean`. Grand MCA is not resolved; no new UNSAFE
witness and no beyond-Johnson SAFE bound are claimed.

## 33. Resolution of the `d = 3` Frobenius-orbit case: the second relation, its sharpness, and the direction-count inverse theorem (`RequestProject/Root/CodingTheory/RationalHyperplaneDescent.lean`, `KoalaBearRigidOrbit3.lean`, `OrbitThreeSharpness.lean`, `KoalaBearOrbitThreeWitness.lean`, `RationalDirectionCount.lean`, `KoalaBearCloseDirections.lean`)

* **The second relation, and its exactness.** `exists_close_rational_hyperplane`: every officially
  bad challenge at orbit dimension three is either *exceptional* (at most one such,
  `exceptional_subsingleton`) or produces a nonzero fixed covector `c` **together with one
  support** `S`, `|S| ≥ n − e`, `¬ LineCloseOn k S f₀ f₁`, on which the whole rational hyperplane
  `c^⊥` is explained by codewords — the *code-good* covectors, `goodCovSet`. The converse
  `isBad_of_mem_goodCovSet` shows the description is exact, so **no third Galois-type relation
  exists**. Refined budget: `card_badSet_mul_le_card_goodCov`, `(#Bad − 1)(q − 1) ≤ #goodCov`.
* **Sharpness: the budget is attained.** `card_badSet_ge_curve`: for the curve pencil
  `f₀(x) = A₀x + A₁x² + A₂x³`, `f₁(x) = x` on the row `k = 1`, `e = |D| − 2`, with `A` any triple
  of full orbit dimension, `|D|(|D| − 1) ≤ 2·#Bad`. Hence `card_badSet_gt_linear`: `#Bad > 2|D|+2`
  already for `|D| ≥ 6`.
* **A Prize-scale `d = 3` witness in the deployed field.** `KoalaRow.orbitThree_card_badSet_ge`
  and `KoalaRow.orbitThree_exceeds_prizeThreshold`: with `D = Fix(Frobenius) = F_p` inside
  `F_{p^6}` and `A` the first three vectors of an `F_p`-basis, `p² − p ≤ 2·#Bad`, so
  `B* < #Bad` by a factor `> 8`. (The row is `k = 1`, radius `n − 2`; this is a **barrier**, not
  a Prize counterexample.) Consequence: **no radius-free `d = 3` safety theorem can exist**, and
  the routes "intersection of two rank-3 linear sets" (`≤ 2p+2`) and "low-degree projective
  annihilator locus" are refuted for official badness.
* **Direction-count inverse theorem.** `card_orthFix` (a nonzero rational covector has exactly
  `q²` rational vectors orthogonal to it) and `card_goodCov_mul_le_card_closeDir` give
  `card_badSet_le_of_closeDir`: `(#Bad − 2)(q − 1)(q² − 1) ≤ #closeDirSet · q²`. Projectively,
  **at least `#Bad − 2` of the `q² + q + 1` rational directions carry an `e`-close word.**
* **Deployed consequence.** `KoalaRow.prizeBreaking_forces_closeDirections` and
  `KoalaRow.prizeBreaking_closeDirection_density`: a Prize-breaking `d = 3` pencil on the deployed
  row forces `B*(p−2) = 585903205788011996252704497 ≤ #closeDirSet` and `p³ < 17·#closeDirSet`,
  i.e. more than `6.05%` of `PG(2,p)` must consist of `e`-close words.
* **Radius barriers on the deployed row.** `KoalaRow.deployed_no_pairwise_rigidity`
  (`n − 2e = 134944 < k`) and `KoalaRow.rigid_orbit3_lt_prizeThreshold` (rigid pencils give
  `#Bad ≤ e + 2 ≪ B*`).

Write-up: `ORBIT_THREE_RESOLUTION_REPORT.md`. Axioms audited in
`RequestProject/RationalHyperplaneAxiomAudit.lean`. Grand MCA is not resolved; no new UNSAFE
witness for the deployed row and no beyond-Johnson SAFE bound are claimed.

## 123. The isotypic decomposition as a single natural isomorphism `diag ≅ forget` (`RequestProject/IsotypicNatIso.lean`)

This closes open item **O9**, the last piece of step 2 of the original brief that was still
missing: the DFT was already available as an algebra isomorphism `F[C_n] ≃ₐ (ℤ/n → F)` and
as an equivalence of categories `Rep F C_n ≌ ModuleCat (ℤ/n → F)`, and the eigenspace
decomposition was available module by module, but not as one Lean `NatIso`.

* `FFT.diagFunctor ζ n : Rep K C_n ⥤ ModuleCat K` — the diagonalisation functor.  On objects
  `X ↦ ⨁_{j < n} ker (ρ(g) − ζ^j)`, on morphisms the direct sum of the restrictions of the
  intertwiner (well defined by `FFT.mapsTo_eigenspace_of_comm`, functorial by
  `DirectSum.toModule` computation rules).
* `FFT.diagNatIso hζ hn : diagFunctor ζ n ≅ Action.forget (ModuleCat K) C_n` — **the natural
  isomorphism** `η : diag ≅ forget`, for `ζ` a primitive `n`-th root of unity and `n`
  invertible in `K`.  Each component is the sum of the inclusions of the eigenspaces, an
  isomorphism by `FFT.cyclic_eigenspace_isInternal`; the naturality square commutes on the
  nose, because an intertwiner maps the `j`-th eigenspace to the `j`-th eigenspace.
* `FFT.diagNatIso_hom_apply` / `FFT.diagNatIso_inv_app` — the isomorphism *is* the DFT:
  forwards it sums the components, backwards it sends `v` to the family of Fourier modes
  `(1/n) ∑_{k<n} ζ^{−jk} ρ(g)^k v` (the projectors `FFT.isoSum` of
  `IsotypicDecomposition.lean`, packaged as the linear map `FFT.dftModes`).
* `FFT.M31.diagNatIso31` — the Mersenne instance: `n = 31`, `ζ = 2`, all eigenvalues bit
  rotations.

No new axioms (`propext`, `Classical.choice`, `Quot.sound` only).  Scope: this is a
statement about representations of `C_n`, not an operation-count statement; nothing about
complexity is claimed here.

## 124. Which circle-FFT twiddles are free rotations? The exact answer (`RequestProject/CircleFreeTwiddles.lean`)

This closes open item **O12**, and the answer is a sharp negative result — the negative
result `TRIAGE.md` predicted from numerics, now proved.

**Mechanism.**  The Chebyshev doubling map `π(x) = 2x² − 1` computes `x`-coordinates of
squares (`FFT.Circle.chebD_x`), so `x(p^{2^k}) = π^k(x(p))`
(`FFT.Circle.x_pow_two_pow`); and a circle point with `x = 1` is the identity
(`FFT.Circle.eq_one_of_x_eq_one`).  Hence

`p^{2^k} = 1 ↔ π^k(p.x) = 1`  (`FFT.Circle.pow_two_pow_eq_one_iff`),

which turns a question about the circle group into a finite iteration in the base field —
no `y`, no square roots, no field extension.  Iterating `π` on the 31 powers of two is a
kernel computation.

**The theorem.**  Over `M31`:

* `FFT.Circle.MersenneFree.x_free_of_pow_eq_one`, `…y_free_of_pow_eq_one` — if a circle
  point has order dividing `2^M` with `M ≤ 27` and one of its coordinates is a power of two,
  then that coordinate is `1` or `2¹⁵`.
* `FFT.Circle.MersenneFree.circleTw_free` — consequently, for **every** circle FFT of the
  project's twiddle tower `circleTw q m k i` with `m + 2 ≤ 27`, at every level `k` and index
  `i`: a twiddle lying in `⟨2⟩` equals `1` or `2¹⁵`.
* `FFT.Circle.MersenneFree.pt45_order` — sharpness: `(2¹⁵, 2¹⁵)` is a genuine point of order
  exactly `8`, so the value `2¹⁵` does occur.
* `FFT.Circle.MersenneFree.pt27_order` — sharpness of the bound `27`: `(2²⁷, 273161206)` has
  order exactly `2²⁸`, so a third free value appears at that size.
* `FFT.Circle.MersenneFree.chebD_two_pow_iff` and `…freeLevel_card` — **the complete table**
  for every size up to the whole circle group `#Circle(M31) = 2³¹`: the number of free
  `x`-values is `1` for `m ≤ 2`, `2` for `3 ≤ m ≤ 27`, then `3, 5, 8, 16` at
  `m = 28, 29, 30, 31`.

**Interpretation.**  `2¹⁵` is exactly `1/√2` in `M31` (`(2¹⁵)² = 2³⁰ = 1/2`), i.e. the
`cos π/4 = sin π/4` twiddle that every radix-8 kernel already special-cases.  So apart from
the trivial twiddle `1`, the Mersenne free-rotation mechanism buys the circle FFT nothing at
any practical size, and the count does not grow with the transform length.  Together with
the earlier base-field statement (multiplication-free DFT lengths over `M31` are exactly `1`
and `31`), the "hidden Mersenne symmetry" hypothesis of the original brief is now closed on
both the base-field and the circle side.

**Sharper still: the free twiddles all sit at the bottom level.**  For a generator `q` of
order exactly `2^(m+2)` with `2 ≤ m` and `m + 2 ≤ 27`:

* `FFT.Circle.MersenneFree.circleTw_not_free_of_pos_level` — at every level `k ≥ 1` (that is,
  everywhere except the single coarsest `x`-level) **no** twiddle is a power of two, so every
  butterfly there costs a genuine multiplication.  The proof is a `2`-adic valuation count:
  a free twiddle forces the corresponding point to be killed by `8`, while `q^{2^{m−k−1}·odd}`
  has order `2^{k+3}`.
* `FFT.Circle.MersenneFree.exists_free_twiddle_level_zero` — and the bottom level really does
  carry one: one of the two level-`0` twiddle values is `2¹⁵` (via
  `FFT.Circle.MersenneFree.x_eq_of_order_eight`: a point of order `8` has `x = ±2¹⁵`, because
  `x(a⁴) = −1` forces `2x² = 1`).

So the entire Mersenne free-rotation mechanism of the circle FFT is confined to one level out
of `m + 1`, where it saves at most half of that level's multiplications.

Scope: the statement is about which twiddle *values* are bit rotations; no benchmark and no
claim about instruction counts, cache behaviour or any existing library is made.

## 125. Step 4 of the Grand MCA programme: the challenge is a symmetric function of the window; the projective additive invariant; gap-one universality (`RequestProject/Root/CodingTheory/SymmetricWindowMechanism.lean`, `ProjectiveCubeRank.lean`, `GapOneUniversality.lean`)

Full write-up: `SYMMETRIC_WINDOW_MECHANISM_REPORT.md`.  Axiom audit:
`RequestProject/SymmetricWindowAxiomAudit.lean` (only `propext`, `Classical.choice`,
`Quot.sound`).

**The mechanism.**  For a window `T` (a circuit, i.e. a `(k+1)`-subset of the domain) put
`winPoly T = ∏_{x∈T}(X−x)`, `winSym i T = e_i(T)` and `winMoment k T m = divDiff k T (x ↦ xᵐ)`.
Then `winPoly_coeff` is Vieta for the window, `winMoment_succ` is the reduction of `X^{k+1+j}`
modulo `winPoly T`, and `winMoment_newton` is the Newton identity
`H_{j+1} = e₁H_j − e₂H_{j−1} + ⋯`, so every moment is the complete homogeneous symmetric
function of the window and depends only on `e₁,…,e_j` (`winMoment_two`: `H₂ = e₁² − e₂`).
Since `divDiff_polyWord_eq_sum_moments` pairs the coefficient vector of a polynomial with the
moments, this gives the **factorisation theorem** `divDiff_polyWord_congr_of_winSym`: a pencil
of degree at most `k + c` cannot distinguish two windows with the same `e₁,…,e_c`.  Hence
`badSet_subset_image_newtonChallenge`: there is one function `Φ : F^c → F` with every bad
challenge of the form `Φ(e₁(T),…,e_c(T))` — the target shape of step 4 of the ten-step plan.

**Gap one, exactly.**  `divDiff_polyWord_gapOne` makes the circuit functional affine in the
window sum, so `isBad_gapOne_mobius_sum`: every bad challenge of a pencil of two polynomials of
degree `≤ k+1` is a Möbius image of a `(k+1)`-subset sum of the domain, with the matrix read off
from the four top coefficients.  At `|D| = k+1+e` this is an equivalence
(`mem_badSet_iff_circuit_gapOne`, `mem_badSet_iff_gapOne_mobius`), and in the degenerate case
(top coefficient pairs proportional) `card_badSet_le_one_of_top_proportional` gives `#Bad ≤ 1`.
The monomial pencil of section 124's predecessor work is the identity-matrix case.

**The right invariant.**  `MobiusCubeRankLe B m` — `B` is the image of a `{0,1}`-cube with `m`
generators under an invertible linear-fractional map, in division-free form.  It keeps the
counting bound (`card_le_two_pow_of_mobiusCubeRankLe`), refines the affine cube rank
(`mobiusCubeRankLe_of_cubeRankLe`), and is covariant for the **full `PGL₂(F)`**
(`MobiusCubeRankLe.mobius_image`) — the symmetry group of the bad set itself, which the affine
invariant does not have.  With it, `gapOne_structure_dichotomy` proves hypothesis H1 of the plan
unconditionally for the whole gap-one class: `#Bad ≤ 1` or `Bad` is additively structured of
Möbius cube rank `≤ |D|`.

**Universality.**  With `Σ = {∑_{x∈T} x : |T| = k+1}`, `card_badSet_gapOne_eq_card_winSums` is
an exact count of the bad set by admissible window sums, whence `#Σ − 1 ≤ #Bad ≤ #Σ`
(`card_badSet_gapOne_le_card_winSums`, `card_winSums_le_card_badSet_succ`) and
`card_badSet_gapOne_pencil_invariant`: at gap one the size of the bad set is not a property of
the pencil at all, only of the domain.  Over a domain with distinct subset sums every
nondegenerate gap-one pencil has `#Bad ≥ C(|D|,k+1) − 1`
(`choose_le_card_badSet_gapOne_succ`); conversely a small gap-one bad set forces the domain to
have few distinct `(k+1)`-subset sums, i.e. real additive structure.

Scope: Grand MCA is not resolved.  The `c ≥ 2` branch (whether the Newton image is small for
multiplicative domains) and steps 5–8 of the plan remain open; no performance claim is made.

## 126. The window system of higher divided differences and the sharp degree threshold (`RequestProject/Root/CodingTheory/HigherDividedDifferences.lean`)

The circuit description of section 125's predecessor uses `C(|S|, k+1)` equations per window,
most of them redundant.  The irredundant form is the vector of *higher* divided differences
`higherDivDiff j S u = coeff_j (interpolant of u on S)`, which vanishes for `j ≥ |S|`:

* `isCloseOn_iff_forall_higherDivDiff` — `IsCloseOn k S u` **iff** `higherDivDiff j S u = 0` for
  all `j ≥ k`; at capacity gap `c` that is exactly `c` linear conditions.
* `isBad_iff_higherDivDiff` — badness of `γ` is exactly: some window `S` of size `≥ |D| − e`
  whose `2 × (|S| − k)` matrix of higher divided differences of the two words annihilates
  `(1, γ)`, with second row not identically zero.
* `higherDivDiff_minor_eq_zero` — hence **the window matrix of a bad challenge has rank one**:
  all its `2 × 2` minors vanish.  These are conditions on the window alone, free of `γ` — the
  determinantal (Schubert) residue of the Newton mechanism predicted by the ten-step plan — and
  `challenge_eq_of_higherDivDiff` then reads `γ` off any column with a nonzero second entry.
* `card_badSet_le_one_of_degree_lt` — **the sharp degree threshold.**  If both received words are
  polynomials of degree below the smallest admissible window size `w` (`w + e ≤ |D|`), the window
  drops out of the system entirely (`higherDivDiff_polyWord_of_degree_lt`: the interpolant is the
  polynomial itself), the relations become conditions on the coefficients alone, and `#Bad ≤ 1`
  at every rate.  The threshold is sharp: the extremal gap-one pencil `X^{k+1}, X^k` has degree
  exactly `k + 1 = |D| − e`, one above the bound, and attains `C(|D|, k+1)`.

So the whole complexity of the MCA bad set switches on at one degree: the received words must
reach the window size before more than one challenge can be bad.

## 127. The exact sub-capacity MCA constant: descent to the defect pair, the fibre partition, and `#Bad = e + 1` (`RequestProject/Root/CodingTheory/ShadowDescentSharpBound.lean`)

Below capacity the size of the bad set of a received line is now known **exactly**, and the
kernel-shadow programme of `FixedShadowLift.lean` is closed in that regime.

* `badSet_sub_polyWord`, `kernelShadow_sub_polyWord` — subtracting a pair of codewords from the
  received pair changes neither the bad set (with its official windows, `isBad_sub_polyWord`)
  nor the kernel shadow of any window: **every object of the theory is an invariant of the
  extended code** `C⁺ = C + ⟨f₀,f₁⟩`.  No hypotheses at all.
* `badSet_descent_dichotomy` — unconditional dichotomy: either `#Bad ≤ 1`, or the received pair
  admits a **witness-preserving strict descent** to a defect pair vanishing outside a set of at
  most `2e` coordinates and having literally the same bad set.  Valid beyond capacity too.
* `exists_window_subset_agreement_of_isBad` + `card_badSet_le_succ_of_global_pair` — the
  mechanism: the official windows cut the defect support `A` into pairwise disjoint nonempty
  fibres, one per challenge, each of size at least `|A| − e`.  Hence `#Bad·(|A|−e) ≤ |A| ≤ 2e`.
* `card_badSet_le_succ_of_third` — therefore `#Bad ≤ e + 1` whenever `1 ≤ k` and `k + 3e ≤ |D|`,
  with `epsMCA_le_succ_of_third` / `epsMCAmax_le_succ_of_third` giving `ε_mca ≤ (e+1)/|F|`.
  This improves `card_badSet_le_third` (`2e + 1`) and `card_badSet_le_two_mul_of_third` (`2e`).
* `exists_badSet_card_succ_of_third`, `exists_badSet_card_eq_succ` — **sharpness**: the defect
  pair supported on `e + 1` domain points with slopes equal to those points realises exactly
  `e + 1` bad challenges.  So `max #Bad = e + 1` in the whole sub-capacity regime.
* `card_inter_add_one_eq_of_kernelShadow_eq_of_not_subset`,
  `card_inter_succ_of_kernelShadow_eq_of_ne` — shadow rigidity **without** the distinct-challenge
  hypothesis of `FixedShadowLift.lean`: equal shadows force `S ⊆ T` or `|S ∩ T| = |S| − 1`.  The
  shadow map is faithful up to one point, so the product bound
  `#Bad ≤ #{shadows} · max #{lifts}` cannot beat the direct count.

Discussion, the exact place where the argument stops beyond capacity, and the separation of
"arbitrary linear code / MDS / RS" hypotheses: `GRAND_MCA_SHADOW_STRUCTURE_REPORT.md`.

## 128. The rank-2 extension `E = C + ⟨f₀,f₁⟩`: exact geometry of `E/C` and the beyond-capacity cluster structure (`RequestProject/Root/CodingTheory/RankTwoExtension.lean`, `RankTwoClusterStructure.lean`, `RankTwoCostBound.lean`, `RankTwoDeployedBoundary.lean`)

The kernel-shadow family is the shortened dual data of one rank-≤2 object, the extension
`E = C + ⟨f₀,f₁⟩`; this section makes that object primary and settles the structure of the
official bad set in terms of it, beyond capacity as well.

* `extCode`, `extDualOn`, `kernelShadow_eq_extDualOn` — `K_S` is exactly the space of parity
  checks of `E` supported inside `S` (dually, the dual of the punctured extension `E|_S`).
* `restrKer`, `restrKer_eq_top_iff_lineCloseOn` — the kernel of the restriction of `E/C` to a
  window, in the coordinates `(α,β) ↦ α f₀ + β f₁`; rank loss two is exactly line-closeness, so
  official noncontainment is exactly the exclusion of rank loss two.
* `isBad_iff_restrKer_eq_span` — **exact reformulation of badness**: `γ` is bad iff some window
  of co-size `≤ e` restricts `E/C` with kernel exactly the projective point `[1:γ]`, i.e. loses
  exactly one rank in the direction of the challenge.  `finrank_restrKer_of_isBad_window` is the
  dimension form, `isBad_iff_exists_light_rep` the coset-leader (weight) form, and
  `mem_restrKer_iff_forall_synMap` identifies `restrKer` with the annihilator of `im Λ_S`.
* `card_badSet_le_one_of_dependent` — if `f₀,f₁` are dependent modulo `C` (`dim E/C ≤ 1`) then
  `#Bad ≤ 1`, with no hypothesis at all: the theory is exactly the rank-two theory.
* `card_le_succ_of_pencil_light` — the sub-capacity fibre argument isolated as a hypothesis-free
  statement about a pencil of words `γ ↦ a + γ·b`.
* `card_badSet_le_succ_mul_succ_card_lowWeight` — **the structure theorem, no hypotheses**:
  `#Bad ≤ (e+1)·(1 + #{c ∈ C : c ≠ 0, wt c ≤ 3e})`.  The bad set is a union of clusters — fibres
  of the deviation map `γ ↦ a + γ·b − v_γ ∈ C` built from light representatives `v_γ` and the
  reference pair `(a,b)` of the witness-preserving descent — each of size at most `e+1`, one per
  low-weight codeword (plus the zero one).  Disjunctive form:
  `card_badSet_le_succ_or_exists_lowWeight`; converse reading:
  `lt_card_lowWeightCodewords_of_card_badSet`.
* `exists_localised_cluster_bound`, `localLowWeightCodewords` — the sharper localised form: for
  one fixed set `A` of at most `2e` coordinates (the descent support) every deviation codeword
  is supported in `A` apart from at most `e` coordinates, and
  `#Bad ≤ (e+1)·(1 + #{c ≠ 0 : wt c ≤ 3e, |supp c ∖ A| ≤ e})`.
* `lowWeightCodewords_eq_empty`, `card_badSet_le_succ_of_capacity` — below capacity the cost set
  is empty and `#Bad ≤ e+1` follows by substitution, without `1 ≤ k` and without interpolation.
* `card_lowWeightCodewords_le`, `card_badSet_le_explicit_cost` — the cost in closed form:
  `#{c ≠ 0 : wt c ≤ w} ≤ C(n, n−w)·q^(k−(n−w))`, hence
  `#Bad ≤ (e+1)·(1 + C(n, n−3e)·q^(k−(n−3e)))`.
* `RankTwoBoundary.*` — boundary-consistency test at `e = 978945`: at rate `1/2` and the
  deployed relative radius the rigid branch would need `n ≥ 5 873 670` while the row has
  `n ≤ 2 092 539`, so the cost branch is the operative one, and the cost is nonvacuous there.

Discussion, hypothesis audit and the single remaining question: `GRAND_MCA_RANK2_EXTENSION_REPORT.md`.

## 129. The residual Reed–Solomon state and residual rigidity

Modules: `RequestProject/Root/CodingTheory/ResidualRSState.lean`,
`RequestProject/Root/CodingTheory/ResidualRSShortening.lean`;
audit `RequestProject/ResidualRSStateAxiomAudit.lean` (36 declarations, only `propext`,
`Classical.choice`, `Quot.sound`).  Discussion: `RESIDUAL_RS_STRUCTURE_REPORT.md`; plan and
refined instruction: `GRAND_MCA_RESIDUAL_PROGRAMME.md`.

* `ResidualRSState k D f₀ f₁` — the output of the witness-preserving descent made a first-class
  object: a codeword pair together with a window `A` outside which both defects vanish.
  `ResidualRSState.badSet_eq` — the residual pair has literally the same bad set.
* `jointDefect k f₀ f₁` — the canonical invariant: the rank of the *smallest* residual state.
  Attained (`exists_residualRSState_jointDefect`), bounded by any exhibited state
  (`jointDefect_le_rank`), and `≤ 2e` once two challenges are bad
  (`jointDefect_le_two_mul_of_one_lt`, from the banked descent).
* **Residual rigidity** (`card_badSet_le_of_supported`, `card_badSet_le_succ_of_jointDefect`):
  `k + |A| + e ≤ |D|` ⟹ `#Bad ≤ e + 1`, and `#Bad ≤ |A|`.  No capacity hypothesis, no `1 ≤ k`.
  The banked sub-capacity theorem is the corollary `card_badSet_le_succ_of_capacity_residual`
  (`k + 3e ≤ |D|`), now hypothesis-free.
* **Slope localisation** (`badSet_subset_image_residualSlope`): under the same hypothesis the
  bad set is *explicitly described* — every bad challenge is a slope `−a(x)/b(x)` of the residual
  pair at one of its support points (`residualSlope`), and if the maximum `e + 1` is attained
  (`e ≥ 1`) the residual support has exactly `e + 1` points, one per challenge
  (`card_pairSupport_eq_of_card_badSet_ge`).  Canonical form:
  `exists_badSet_subset_image_residualSlope`.
* **Shortening geometry**: `shortCode k B = Short(C,B)` with the exact criterion
  `shortCode_eq_bot_iff : Short(C,B) = 0 ↔ (B = ∅ ∨ k + |B| ≤ |D|)`, and the conceptual form of
  rigidity `card_badSet_le_succ_of_no_invisible_direction`: if every `Short(C, A ∪ Z)`,
  `|Z| ≤ e`, vanishes then `#Bad ≤ e + 1`.  `exists_shortCode_ne_bot_of_residual` gives the
  converse existence of an invisible direction past the threshold.
* **Localised cost** (`card_localLowWeightCodewords_le`, `card_badSet_le_residual_cost`): for
  `3e ≤ |D|`, unconditionally `#Bad ≤ (e+1)(1 + C(|D|,e)·q^(k−(|D|−3e)))`; the banked global
  form has `C(|D|,3e)`.
* **Boundary audit** (`le_jointDefect_polyWord_pow`,
  `not_residual_hypothesis_polyWord_pow`): the gap-one pencil has joint defect `≥ |D| − k`, so
  the residual hypothesis fails for it — as it must, since that family is superpolynomially bad.
* **Sharpness beyond capacity** (`ResidualRSSharpness.exists_badSet_card_eq_succ_residual`): for
  every `k + 2e + 1 ≤ |D|` there is a received pair with exactly `e + 1` bad challenges (the pair
  `b = 1_T`, `a = −x·1_T` on `|T| = e + 1` domain points, whose slopes are the points themselves).
  For `e ≥ 2` this covers instances with `k + 3e > |D|`, where the banked sub-capacity
  construction does not apply.
* **The obstruction, isolated** (`lt_card_of_card_badSet_gt`): descent gives `r ≤ 2e`, rigidity
  needs `r ≤ |D| − k − e`; composing them yields exactly `#Bad > e+1 ⟹ |D| < k + 3e`.  Closing
  Grand MCA in this language means closing the gap between `2e` and `|D| − k − e`.

## 130. The theory of residual absorption: the joint defect as canonical invariant, and the sharp bound for arbitrary linear codes (`RequestProject/Root/CodingTheory/ResidualAbsorption.lean`, `ResidualAbsorptionCost.lean`, `ResidualAbsorptionSequence.lean`, `ResidualAbsorptionSharp.lean`)

Discussion: `GRAND_MCA_RESIDUAL_ABSORPTION_REPORT.md`.  Axiom audit:
`RequestProject/ResidualAbsorptionAxiomAudit.lean` (54 declarations, only `propext`,
`Classical.choice`, `Quot.sound`).  Everything is stated for an **arbitrary linear code
`C ⊆ A^ι` over an arbitrary alphabet**; Reed–Solomon appears only in the corollaries.

* **What absorption is.**  A residual state is a pair of representatives `(f₀ − q₀, f₁ − q₁)`,
  `q₀,q₁ ∈ C`; the states form a torsor under `C × C` and absorbing an invisible codeword is
  translation in that torsor.  The operation is semantics-preserving: `agreeOn_residual_iff`,
  `lineAgreeOn_residual_iff`, `isBad_residual_iff`, `badSet_residual_eq`,
  `cosetWeight_residual_eq`, `jointDefect_residual_eq`.  So the whole MCA datum is an invariant
  of the rank-two extension `E = C + ⟨f₀,f₁⟩`.
* **The invariant it reduces** is the joint support; its terminal value is
  `jointDefect C f₀ f₁` (`exists_minimal_state`, `exists_terminal_descent`), which dominates the
  pointwise distance at every challenge (`cosetWeight_lineComb_le_jointDefect`), satisfies the
  unique-decoding terminality criterion `2r < d ⟹ jointDefect = r`
  (`jointDefect_eq_of_two_mul_lt`), and drops to `≤ 2e` as soon as two challenges are bad
  (`jointDefect_le_two_mul_of_one_lt`).
* **Residual Absorption Theorem** (`card_badSet_le_succ_of_noCore`): if `C` has no nonzero word
  of weight `≤ jointDefect + e` (`NoCore`), then `#Bad ≤ e + 1` and `#Bad ≤ jointDefect`.
  Close-set form `card_goodZ_le_succ_of_noCore`, trichotomy `absorption_trichotomy`, equality
  case `jointDefect_eq_succ_of_card_badSet_eq`, converse `exists_core_of_card_badSet_gt`.
* **The drop divisor** (`sum_card_challengeZeros_le`, `card_mul_sub_le`,
  `card_le_succ_of_light`): hypothesis-free — the total drop of a state over the whole
  projective line is at most its rank.
* **General unique-decoding bound** (`card_badSet_le_succ_of_minDist`): for *any* linear code
  over *any* alphabet, `3e < d ⟹ #Bad ≤ e + 1`.  This improves
  `Alphabet.card_badSet_le` (bound `|ι|`) to the sharp constant and removes the Reed–Solomon
  structure and `1 ≤ k` from `card_badSet_le_succ_radius`; the Reed–Solomon statement is
  recovered as `card_badSet_rs_le_succ`.
* **Finite structural cost** (`card_goodZ_le_succ_mul_card_image`, `absorption_dichotomy`):
  beyond the correlated-agreement branch, `#close ≤ (e+1)·#image Φ` where `Φ` is the deviation
  map, whose values are `0` or invisible cores of weight `≤ jointDefect + e`; with no core the
  image is `{0}` and the bound collapses to `e + 1` (`card_goodZ_le_of_no_core`).
* **The absorption exact sequence** (`extension_inf_sup_eq`, `finrank_kernelShadow`):
  `0 → Short(C,Z) → Short(E,Z) → K_Z → 0`, so a rank loss of the extension at `Z` is a word of
  `E` supported in `Z`, counted modulo the invisible cores.  Also
  `noCore_iff_shortening_eq_bot` (the hypothesis *is* the vanishing of all small shortenings)
  and `cosetWeight_le_iff_exists_window` (closeness is membership in the filtration `C ⊔ P_Z`).
* **Sharpness at `3e = d`**: the banked hole witness has `3 ≤ jointDefect ≤ 4`
  (`three_le_jointDefect_hole`, `jointDefect_hole_le`) and carries an invisible core
  (`exists_core_hole`); hence `3e ≤ d` does not suffice
  (`not_forall_card_badSet_le_succ_of_three_mul_le`).  The descent stops exactly where the
  first invisible core appears.

## 131. The structure of a family of absorbed invisible cores: torsor over a shortening, two-jump filtration, and terminal-or-core (`RequestProject/Root/CodingTheory/AbsorbedCoreModule.lean`, `AbsorbedCoreDirections.lean`, `AbsorbedCoreDescent.lean`, `AbsorbedCoreFiltration.lean`, `AbsorbedCoreExactSequence.lean`, `AbsorbedCoreWitness.lean`)

Everything here is for an arbitrary linear code over an arbitrary alphabet module; discussion in
`GRAND_MCA_ABSORBED_CORE_STRUCTURE_REPORT.md`, axiom audit
`RequestProject/AbsorbedCoreAxiomAudit.lean`.

* **Torsor theorem** (`absorbedCores_bijOn_corePairs`, `absorbedCores_eq_coset`): the family of
  absorbed invisible cores at a window `W` — the core pairs whose absorption leaves a residual
  state supported in `W` — is empty or an affine space over the module
  `corePairs C W = Short(C,W) × Short(C,W)`.  Its structure depends only on the code and the
  window, never on the received pair.  Differences of absorbed cores *are* the invisible cores
  hidden by the window (`sub_mem_corePairs`, `add_mem_absorbedCores`).
* **Lattice behaviour**: `absorbedCores_inter`, `shortening_inter`, `shortening_mono`,
  `mem_absorbedCores_jointSupport` (least window = joint support).
* **Complexity is paid for in rank**: `finrank_shortening_le` gives the Singleton-type bound
  `dim Short(C,W) ≤ (|W| + 1 − d)·dim A`, hence `dim ≤ 2(|W| + 1 − d)·dim A` for the family
  (`finrank_corePairs`, `absorbed_core_family_structure`); conversely
  `finrank_shortening_add_dist_le` and `dist_le_card_of_shortening_ne_bot` say a `t`-dimensional
  core family forces `d + t ≤ |W| + 1`.
* **Terminal or core** (`terminal_or_core`, `subsingleton_absorbedCores_of_noCore`,
  `exists_core_of_ne`): at every window the family is a single point or the code has a nonzero
  word of weight `≤ |W|`; no intermediate behaviour.  Instance-independent container:
  `lowWeightCore`, `sub_mem_lowWeightCore`, `lowWeightCore_eq_bot_iff` (`= ⊥ ↔ NoCore`).
* **Rank-loss directions** (`lostDirections`): a subspace of `F²`, monotone in `W`, equal to `⊤`
  exactly when the state collapses into `W` (`lostDirections_eq_top_iff_nonempty`).  Two
  independent lost directions force `⊤` (`eq_top_of_det_ne_zero`), whence the trichotomy
  `lostDirections_trichotomy`: nothing, a single projective point — the fixed shadow
  (`exists_span_of_ne_bot_of_ne_top`) — or collapse.  Consequences:
  `challenge_unique_or_collapse`, `explained_subsingleton_or_all`, and
  `jointDefect_le_two_mul_of_two_close` (two distinct `e`-close challenges force rank `≤ 2e`).
* **Two-jump filtration**: `pencilDefect = min{|W| : Lost(W) ≠ ⊥} ≤ jointDefect = min{|W| :
  Lost(W) = ⊤}` (`pencilDefect_le_card_of_ne_bot`, `exists_window_card_eq_pencilDefect`,
  `jointDefect_le_card_of_eq_top`, `exists_window_card_eq_jointDefect`,
  `pencilDefect_le_jointDefect`).  The pair is strictly finer than the scalar joint defect: the
  `𝔽₂` witness of `AbsorbedCoreWitness.lean` has `pencilDefect = 1 < 2 = jointDefect` with an
  explicit fixed shadow (`pencilDefect_lt_jointDefect_witness`, `exists_fixed_shadow`).
* **Exact sequence in dimensions** (`finrank_lostDirections_add_finrank_shortening`):
  `dim Lost(W) + dim Short(C,W) = dim Short(E,W) + dim Lost(∅)`; for a genuinely rank-two state
  `dim Lost(W) = dim Short(E,W) − dim Short(C,W)` (`finrank_lostDirections_of_dep`), and the
  extension hides at most two dimensions more than the code
  (`finrank_shortening_extension_le`).  Membership form:
  `mem_lostDirections_iff_sup_shortening`.
* **Terminal or descent, no hypotheses** (`canonical_terminal_or_core`): either the rank-minimal
  residual state is unique — a canonical normal form — or the code has a nonzero invisible core
  of weight `≤ 2·jointDefect`.  Hence `exists_unique_minimal_state` for `2·jointDefect < d`, with
  step form `descent_or_minimal` and `exists_core_of_stateRank_lt`, and the combined statement
  `canonical_state_and_badSet` (unique canonical state together with `#Bad ≤ e + 1`).

## 132. The universal Lost-filtration of a nested pair of codes: one exact sequence with Rank2, fixed shadows and residual absorption as corollaries (`RequestProject/Root/CodingTheory/LostFiltration.lean`, `LostFiltrationSpectrum.lean`, `LostFiltrationInformationSet.lean`, `LostFiltrationMDS.lean`, `LostFiltrationRankTwo.lean`, `LostFiltrationTorsor.lean`)

Discussion: `GRAND_MCA_LOST_FILTRATION_REPORT.md`.  Axiom audit:
`RequestProject/LostFiltrationAxiomAudit.lean` (77 declarations, only `propext`,
`Classical.choice`, `Quot.sound`).

* **The object.**  For an arbitrary nested pair of `F`-linear codes `C ≤ E` in `ι → A` and a
  window `W`, `lostStage C E W = E ⊓ (C ⊔ P_W)` — the part of `E` invisible modulo `C` after
  deleting `W`.  It is a monotone, exhaustive filtration of the interval `[C,E]`
  (`lostStage_empty`, `lostStage_univ`, `lostStage_mono`), packaged as an order homomorphism
  `lostStageHom` and functorial in the pair (`lostStage_mono_left`, `lostStage_mono_right`).
* **The universal exact sequence** (`lostStage_eq_sup_shortening`): `Lost(C,E,W) = C ⊔
  Short(E,W)`, i.e. `0 → Short(C,W) → Short(E,W) → Lost(C,E,W)/C → 0`.  The invisible cores are
  the kernel of the filtration.
* **Lattice law and its exact obstruction**: `lostStage_inter` (meet-preserving whenever
  `Short(C, W ∪ W') = ⊥`; `lostStage_inter_of_noCore`), sharp by the two-position witness
  `repCode_lostStage_inter_ne` together with `repCode_shortening_ne_bot`.
* **Defect spectrum** `relDefect C E j = min{|W| : dim Lost(C,E,W) ≥ dim C + j}` — the relative
  weight hierarchy.  Deletion bound `finrank_lostStage_erase_le` (one position costs at most
  `dim A`), hence strict monotonicity `relDefect_lt_succ` and `le_relDefect` over a
  one-dimensional alphabet; Singleton laws `finrank_le_finrank_lostStage_add`, `relDefect_le`,
  and the distance-refined `relDefect_le_of_minDistGe`, `le_relDefect_of_minDistGe`; the two
  ends `relDefect_one_le_card_support` / `exists_word_of_relDefect_one` and
  `lostStage_eq_top_iff` / `exists_window_lostStage_eq_top`.
* **Information sets and the sharp Singleton law**: `exists_information_set` (every linear code
  has an information set — a rigid set of `dim E` positions, `Short(E,Iᶜ) = ⊥`), with the
  surjectivity form `exists_mem_agree_on_information_set`; hence
  `lostStage_compl_information_set`, `relDefect_top_le_sub_finrank` (`δ_r ≤ n − dim C`), the jump
  separation `relDefect_add_le`, and the **sharp relative Singleton law**
  `relDefect_le_sharp`: `δ_j ≤ n − dim E + j`.
* **Evaluation codes** (`relDefect_eq_of_mds`): if the big code of a nested pair is MDS of
  dimension `k'` — no hypothesis on the subcode — then `δ_j = n − k' + j` for `1 ≤ j ≤ k' − k`,
  so the hierarchy is maximal.  Reed–Solomon instance `relDefect_reedSolomon`:
  `δ_j(RS_k, RS_{k'}) = |D| − k' + j`.
* **Rank2 as a corollary**: for a genuinely rank-two state (`Dep = ⊥`), `dim E = dim C + 2`
  (`finrank_extension_of_dep`), `pencilDefect = δ_1` (`pencilDefect_eq_relDefect_one`) and
  `jointDefect = δ_2` (`jointDefect_eq_relDefect_two`); hence over a field alphabet
  `pencilDefect < jointDefect` **strictly** (`pencilDefect_lt_jointDefect`), sharpening the
  banked `pencilDefect_le_jointDefect` — the fixed-shadow band is never empty.  The quantitative
  trichotomy is `rank_two_regime_classification`, and for a code of dimension `k` the whole
  picture sits in `pencilDefect ≤ n − k − 1 < jointDefect ≤ n − k` with no hypothesis on the code
  (`jointDefect_le_sub_finrank`, `pencilDefect_le_sub_finrank`; the MDS special cases are
  `pencilDefect_le_of_mds`, `jointDefect_le_of_mds`).
* **The torsor as the kernel side**: `absorbedCores_nonempty_iff_lostStage_eq` (nonempty exactly
  at the top of the filtration), `corePairs_eq_bot_iff`, `exists_unique_corePair`,
  `absorbedCores_vadd_bijective`.
* **Scope.**  Two Singleton laws are proved: the elementary `δ_j ≤ n − (dim E − dim C) + j` and
  the sharp relative one `δ_j ≤ n − dim E + j`, an equality when the big code is MDS.  Strict
  monotonicity, the sharp law and the information-set construction assume `dim A = 1`.  No
  performance or implementation claim is made.

## 133. The canonical residual class of the Lost-filtration: one object behind the quotients, the restriction kernel and the absorbed-core torsor (`RequestProject/Root/CodingTheory/LostFiltrationResidual.lean`, `LostFiltrationResidualTriple.lean`, `LostFiltrationResidualDescent.lean`, `LostFiltrationResidualMDS.lean`)

For a nested pair `C ≤ E` and a window `W` the **residual class** `Res(C,E,W)` is the image of
the Lost-filtration stage in the fixed ambient quotient `(ι → A)/C` (`residual`): a submodule,
defined with no choice of representative, from which `Lost` is recovered by `comap`
(`comap_mkQ_residual`).

* **Canonical quotient theorem.**  `Lost(C,E,W)/C ≅ Res(C,E,W)` (`residualEquivLostQuot`) and
  `Short(E,W)/Short(C,W) ≅ Res(C,E,W)` (`residualEquivShorteningQuot`), hence the comparison
  isomorphism of the universal exact sequence (`lostQuotEquivShorteningQuot`).
* **Universal property** (`residual_universal`): `Res` with `resMk` is the cokernel of
  `Short(C,W) → Short(E,W)`; every linear invariant of window-supported words of `E` vanishing on
  the invisible cores factors uniquely through it.
* **Restriction kernel** (`residual_eq_inf_ker_punctureQuot`): `Res` is exactly the part of `E/C`
  killed by the restriction to the complement of the window.
* **Torsor comparison** (`absorbedCores_nonempty_iff_residual_eq_top`,
  `lostDirections_eq_comap_residual`): the rank-two lost directions are the pullback of `Res`, and
  the absorbed-core family is nonempty exactly when `Res = E/C`.
* **Persistence and exactness.**  `residualHom` is an increasing filtration of `E/C` by submodules
  of one fixed module, meet-preserving modulo invisible cores (`residual_inter`); along a tower
  `C ≤ D ≤ E` there is a short exact sequence `0 → Res(C,D,W) → Res(C,E,W) → Res(D,E,W) → 0`
  (`residualTripleEquiv`) and dimensions add (`finrank_residual_add_triple`).
* **Intrinsic spectrum.**  `dim Res = dim Short(E,W) − dim Short(C,W)`, so `δ_j` is the jump
  sequence of `dim Res(C,E,·)` (`relDefect_eq_sInf_residual`).
* **Exact gluing obstruction.**  With `gluingDefect M W W' = dim Short(M,W∪W') − dim(Short(M,W) ⊔
  Short(M,W'))`: `dim Res(W) + dim Res(W') + gluingDefect E = dim Res(W∩W') + dim Res(W∪W') +
  gluingDefect C` (`residual_budget_identity`), and the defect vanishes exactly when the gluing is
  exact (`gluingDefect_eq_zero_iff`).
* **Canonical residualization.**  Terminal windows are closed under intersection away from the
  invisible cores (`terminalWindow_inter`); under `NoCore C (2m)` a smallest terminal window of
  size `≤ m` exists, is contained in every other one (`exists_min_terminalWindow`), and carries a
  unique absorbed residual state (`absorbedCores_min_terminalWindow_unique`).
* **MDS/RS classification.**  `dim Short(E,W) = |W| + dim E − n` for MDS codes
  (`finrank_shortening_of_mds`), hence exactly three residual regimes, determined by `|W|` alone
  (`residual_regime_trichotomy`), with the Reed–Solomon instance
  (`finrank_residual_reedSolomon`).
* **Scope.**  The MDS section assumes a one-dimensional alphabet and Singleton-tight distance for
  both codes.  No identification of `Res` with a dual-side kernel-shadow object is claimed; see
  `GRAND_MCA_RESIDUAL_CLASS_REPORT.md`.  Axiom audit:
  `RequestProject/LostFiltrationResidualAxiomAudit.lean`.

## 134. Support-covering triples: an unconditional dichotomy turning a large official bad-support family into either a nonzero obstruction or the finite challenge cost `B* = e + 1` (`RequestProject/Root/CodingTheory/BadSupportCoveringTriple.lean`)

For an **arbitrary** `F`-linear code `C ≤ (ι → A)` over an **arbitrary** alphabet, a
*bad-support family* is a finite set of challenges together with a chosen official bad support
for each (`|Sᶜ| ≤ e`, the window explains its own point of the line but not the whole line);
`exists_badSupportFamily` extracts one from any finite set of officially bad challenges, in
particular from the whole `badSet`.  Write `Covering C S` for `Short(C, Sᶜ) = ⊥` — no invisible
core outside `S`, equivalently `S` contains an information set.

* **Line-class bound** (`card_lineClass_le_card_compl`, `card_lineClass_le`), unconditional: one
  codeword line `γ ↦ p₀ + γ·p₁` explains at most `|(supp γ₀)ᶜ| + 1 ≤ e + 1` challenges of the
  family, for every `γ₀` it explains.  A challenge explained by the line must disagree with it
  on its own support (else its support would explain the whole line), that position determines
  the challenge, and the positions therefore lie in one fixed set of size `≤ e`.
* **The dichotomy** (`card_le_or_exists_obstruction`), unconditional: either `#chal ≤ e + 1`, or
  there are three pairwise distinct challenges of the family and an explicitly exhibited nonzero
  `z ∈ Short(C, (S₁ ∩ S₂ ∩ S₃)ᶜ)` of weight `≤ 3e` — a failed support-covering triple.  No
  window hypothesis `e·|B| + k ≤ n`, no rate, distance or non-degeneracy hypothesis.
* **Finite-cost branch** (`card_chal_le_of_covering`, `card_chal_le_of_noCore`,
  `card_badSet_le_succ_radius`, `card_badSet_le_succ_radius_of_minDist`): `NoCore C (3e)` — in
  particular `3e < d` — gives `#Bad ≤ e + 1`, strengthening `Alphabet.card_badSet_le`
  (`#Bad ≤ n`) at the same hypothesis and in the same generality.  Consequently
  `ε_mca ≤ (e+1)/|F|` (`epsMCA_le_of_noCore`) and `ε_mca ≤ 2⁻¹²⁸` whenever `(e+1)·2¹²⁸ ≤ |F|`
  (`epsMCA_le_prize_threshold`).
* **Transport** (`covering_interleavedCode_iff`, `noCore_interleavedCode`,
  `card_badSet_interleaved_le_succ_radius`): covering and `NoCore` are interleaving invariants,
  so the interleaved code `C^⋈κ` — the shape of the deployed extension-field instance — inherits
  `B* = e + 1` from the base code.
* **Other readings of covering**: dual/kernel-shadow (`covering_iff_dual_finrank`:
  `dim Short(C^⊥, S) = |S| − dim C`), matroid (`exists_two_codewords_of_not_covering`: no
  information set), `Res`-filtration (`covering_iff_lostStage_bot`), and the MDS/RS regime
  (`covering_of_mds`, `card_badSet_le_of_mds`: `k + 3e ≤ n`).
* **Structural branch**: `card_le_or_relDefect_one_le` — either `#chal ≤ e + 1` or the first
  jump `δ₁` of the `Res`-filtration of `⊥ ≤ C` is `≤ 3e`; and the obstruction is charged to a
  gluing defect (`finrank_shortening_union_three`,
  `one_le_gluingDefect_sum_of_not_covering`): under `NoCore C e` the three complementary windows
  have exactly additive budgets and a failed triple forces their sum to be `≥ 1`.
* **Scope.**  No list-decoding argument is used and no bound is claimed in the structural
  branch: the banked gap witnesses show that none of this shape can hold once `d ≤ 3e`.  MDS
  statements assume a one-dimensional alphabet; the dual statements are for `A = F`.  Narrative:
  `SUPPORT_COVERING_TRIPLE_REPORT.md`.  Axiom audit:
  `RequestProject/BadSupportCoveringTripleAxiomAudit.lean`.

## 135. The maximal correlated agreement `τ`: the sharp invariant of the second-moment mechanism, and the exact residual gate (`RequestProject/Root/CodingTheory/MaximalCorrelatedAgreement.lean`)

* **The invariant.**  `τ(f₀,f₁) = max { |{x : f₀ x = q₀ x ∧ f₁ x = q₁ x}| : q₀,q₁ ∈ C }`
  (`mcaTau` for an arbitrary linear code over an arbitrary alphabet module, `rsTau` for
  Reed–Solomon).  It is an invariant of the residual plane: `mcaTau_add_mem`
  (`τ(f₀+c₀,f₁+c₁) = τ(f₀,f₁)`), `mcaTau_swap`, and the maximum is attained
  (`exists_pair_card_eq_rsTau`).
* **Master counting theorem** (`card_le_of_pairAgreement_bound`, `card_le_of_mcaTau`):
  for any family `B` of challenges with witness windows of size `≥ t`,
  `#B·(t² − N·τ) ≤ N·t`.  The pairwise input is forced by the two-witness codeword pair
  (`inter_subset_pairAgree`); no noncontainment, distance, rate or window hypothesis is used.
  Reed–Solomon form for the official bad set: `card_badSet_le_of_rsTau`,
  `card_badSet_le_of_rsTau_div`, `epsMCA_le_of_rsTau`.
* **Strictly sharper than the previous far branch.**  `card_badSet_le_far_of_rsTau_lt` recovers
  `card_badSet_le_setFamilyJohnson_of_far` as the case `c = k+e−1`.  Since `k ≤ τ` always
  (`rsTau_ge_dim`), the mechanism's exact ceiling is `|D|·k < t²`, i.e. the full Johnson radius
  `(1−δ)² > ρ` (`johnson_branch_needs_johnson_radius`), against the old `(1−δ)² > ρ+δ`.
  Concretely at `ρ = 1/2`, `|D| = 2²⁰`, `e = 300000` (`δ ≈ 0.2861`):
  `card_badSet_le_rho_half_example` gives `#Bad ≤ 73` for lines with `τ = k`, where the old
  branch is inapplicable (`rho_half_example_old_branch_fails`).
* **`τ` is the correlated-agreement invariant** (`exists_lineCloseOn_iff_le_rsTau`): a window of
  size `s` carrying the whole line exists iff `s ≤ τ`.  Hence the master reduction
  (`correlatedAgreement_or_rsTau_window`): every line either satisfies the MCA conclusion at
  radius `e`, or has `k ≤ τ < |D| − e`, a window of width exactly the capacity gap.
* **Deployed audit** (`|D| = 2²¹`, `k = 2²⁰`, `e = 978944`):
  `deployed_correlatedAgreement_or_window` — either MCA, or `1048576 ≤ τ < 1118208` (width
  `69632`);  `deployed_johnson_branch_empty` / `deployed_johnson_deficit` — the second-moment
  branch is vacuous there, by the exact deficit `|D|·k − t² = 948634124288`;  `deployed_gate` —
  the pinning branch gives `#Bad ≤ 978945` when `τ ≥ k+e`, which is above the correlated-agreement
  threshold and so adds nothing inside the window.
* **Scope.**  No bound on `#Bad` is claimed inside the residual window; what is proved there is
  the reduction and the impossibility of any second-moment route.  Narrative:
  `MAXIMAL_CORRELATED_AGREEMENT_REPORT.md`.  Axiom audit:
  `RequestProject/MaximalCorrelatedAgreementAxiomAudit.lean`.

## 136. Classification of the narrow `τ`-window: the window gauge, the window mass, the zero-witness bound and the residual descent (`RequestProject/Root/CodingTheory/TauWindowClassification.lean`, `TauWindowExtremal.lean`)

The remaining gate was: bound `#Bad` for lines whose maximal correlated agreement lies in
`k ≤ τ = k+s < n−e`, a window of width `w = n−k−e` (deployed `69632`).  This section classifies
that window with one new invariant and no second-moment, Johnson or list-decoding input.

* **The gauge.**  `rsTau_sub_poly` and `isBad_sub_poly`: `τ` and the bad set are unchanged when
  codewords are subtracted from the two words.  `exists_normalisedWindow`: after subtracting a
  `τ`-attaining pair there is a window `A` with `f₀ = f₁ = 0` on `A` and `|A| = τ` maximal
  (`NormalisedWindow`).  `normalisedWindow_eq_commonZeroSet`: in this gauge `A` *is* the common
  zero set, so outside `A` the words never vanish together, and
  `subsingleton_challenge_of_notMem`: every position outside `A` pins at most one challenge.
  `eq_of_two_challenges_same_window`: two challenges explained on the same window force
  `|S| ≤ τ`, so inside the window distinct bad challenges have distinct witness windows.
* **The invariant.**  `windowMass A p = #{x ∈ A : p(x) ≠ 0}` — the errors a challenge spends
  inside the correlated window.  `isBad_dichotomy`: a bad challenge is either *zero-witness*
  (`a = 0`, equivalently the witness codeword is `0`, `eq_zero_of_windowMass_zero`) or has
  `s + 1 ≤ a ≤ e` (`windowMass_ge_of_ne_zero`, `windowMass_le_of_witness`) with agreement
  `|S ∖ A| ≥ (w−s) + a` (`card_sdiff_window_ge`).  `card_inter_sdiff_window_le` — exact challenge
  transport: `|(S ∩ S′) ∖ A| ≤ a + a′`.
* **The bound (zero-witness branch).**  The zero sets outside `A` are pairwise disjoint of size
  `≥ w − s`, so `card_zeroWitnessBadSet_mul_le`: `#Bad₀·(w−s) + τ ≤ n`; divided form
  `card_zeroWitnessBadSet_le_div` (`#Bad₀ ≤ (n−k−s)/(w−s) = 1 + e/(w−s)`) and the uniform
  `card_zeroWitnessBadSet_le_succ` (`#Bad₀ ≤ e+1`).  Deployed: `≤ 15` at `s = 0`
  (`deployed_zeroWitness_le_fifteen`) and `≤ 978945` for every `s < 69632`
  (`deployed_zeroWitness_le`) — far below `B* ≈ 2⁵⁷·⁹`.
* **The mass-bounded branch.**  `card_le_of_massBounded`: with the mass-weighted transport in
  place of the (useless) pairwise bound `τ`, a family of challenges of window mass `≤ a` and
  agreement `≥ W` outside the window obeys `#B·(W² − |D|·2a) ≤ |D|·W`.  This is a counting on the
  residual window, not the empty global second-moment branch; deployed instance
  `deployed_massBounded_le`: at `s = 0`, all bad challenges of window mass `≤ 1000` number
  `≤ 223`.
* **The residual descent (positive-mass branch).**  `witness_shortened_factorisation` /
  `witness_shortened_degree`: the witness is divisible by the vanishing product of the `τ − a`
  window positions off its mass, with quotient of degree `< a − s`.  On `B = Aᶜ` the residual
  instance is `(n₁,k₁,e₁) = (n−τ, a−s, e−a)` and `residual_parameters` gives `n₁ = k₁+e₁+w`: the
  capacity gap is preserved exactly, while `k₁ ≤ e−s < k` whenever `e < k` (`residual_dim_lt`),
  the deployed regime.  `tauWindow_master` packages all of this for an arbitrary line.
* **Sharpness and necessity of the split** (`TauWindowExtremal.lean`, `decide`-checked): the line
  `f₀ = (0,0,2,1,0)`, `f₁ = (0,1,3,2,0)` over `ZMod 5` with `k = 1`, `e = 2` has `τ = 2 = k+1`,
  `τ < t = 3`; its zero-witness bad set has exactly `3` elements — the bound `(n−k−s)/(w−s) = 3`
  is attained (`zeroWitnessBadSet_card_eq_three`) — while its full bad set has at least `4`
  (`four_le_card_badSet`, `zeroWitness_lt_badSet`).  Hence `(n−k−s)/(w−s)` is *not* a bound for
  the whole bad set and the zero-witness restriction is necessary.
* **Scope.**  No bound is claimed on the positive-mass branch; for masses above
  `≈ e − √(e² − (w−s)²)` the pairwise data of `card_inter_sdiff_window_le` is satisfiable by
  arbitrarily large families, so progress there must use the shortened-code structure, not
  counting.  Narrative: `TAU_WINDOW_CLASSIFICATION_REPORT.md`.  Axiom audit:
  `RequestProject/TauWindowClassificationAxiomAudit.lean`.

## 137. `BranchingControl`: the canonical family-level residual recursion of the `τ`-window (`RequestProject/Root/CodingTheory/BranchingControl.lean`)

`TauWindowClassification` (§136) produces, for each positive-mass bad challenge separately, a
residual instance; it does not relate the parent bad set to the bad sets of finitely many *fixed*
child instances.  This section supplies that recursion.

* **The canonical child class.**  For a positive-mass official witness `p` (`p ≠ 0`, `deg p < k`,
  agreement `≥ t = n − e`), its child class is `Z = windowZeros A p = {x ∈ A : p(x) = 0}`,
  `|Z| = τ − a`.  It determines the child completely: domain `resDomain D A = D ∖ A`
  (`n₁ = n − τ`), dimension `resDim k Z = k − |Z| = a − s`, radius `resRad e A Z = e − a`, and
  words `resWord A Z f_i = f_i / V_Z` where `V_Z = vanishPoly Z = ∏_{z ∈ Z}(X − z)` is nonzero on
  `D ∖ A` (`eval_vanishPoly_res_ne_zero`).  Dividing by `V_Z` turns the shortened code
  `V_Z · RS_{k₁}` into an honest `RS_{k₁}(D ∖ A)`: the child is an instance of the same problem.
* **Exact witness transport.**  `witness_eq_vanishPoly_mul` (`p = V_Z·r`, `r ≠ 0`, `deg r < k₁`),
  `resWord_witness` (the residual line point equals `r` on the residual support),
  `card_resSupport` (`|S₁| = |S ∖ A|`).
* **The child is again bad.**  `mem_resBadSet_of_positiveMass`: `γ ∈ badSet k₁ e₁ g₀ g₁` over
  `D ∖ A`, including the negative half of `IsBad` — closure of the child line on `S₁` would give
  codewords `V_Z·q₀`, `V_Z·q₁` correlating with `(f₀,f₁)` on `(S ∖ A) ∪ Z`, of size `≥ n − e > τ`,
  contradicting window maximality.
* **Invariants of the descent.**  `child_capacity_gap`: `n₁ = k₁ + e₁ + w` — `w` is preserved
  exactly.  `child_radius_lt`: `e₁ < e`; `child_dim_le`: `k₁ ≤ k`; `child_complexity_lt`:
  `k₁ + e₁ < k + e`.  Base case `card_badSet_le_one_of_radius_zero`: at radius `0` a line has at
  most one bad challenge.
* **Fibring and multiplicity.**  `childClasses k e A = {Z ⊆ A : |Z| < k, |A| ≤ |Z| + e}` (exactly
  `s + 1 ≤ a ≤ e`); `badSet_subset_terminal_union_children`:
  `Bad ⊆ Bad₀ ∪ ⋃_{Z ∈ children} Bad(child Z)`; `card_childClasses_le`:
  `#children ≤ ∑_{j ∈ [τ−e,k)} C(τ,j)`, `card_childClasses_le_pow`: `≤ 2^τ`.
  `child_class_unique_of_uniqueDecoding`: for `k + 2e ≤ n` the class `Z` does not depend on the
  choice of official witness.
* **The recurrence.**  `branchingControl`: `#Bad ≤ #Bad₀ + Σ_Z #Bad(child Z)`;
  `branchingControl_terminal` replaces `#Bad₀` by `e + 1`; `branchingControl_recurrence` lifts any
  child bound `G`; `branchingControl_budget`: `#Bad ≤ (e+1) + N·L` under budgets;
  `exists_large_child` is the pigeonhole (some child carries a `1/#children` share).
  `branchingControl_master` is the target trichotomy: the recurrence together with
  `#Bad ≤ (e+1)+N·L ∨ N < #children ∨ ∃ Z, BranchingCertificate … (L+1) …`, where the certificate
  records a single child with preserved gap `w`, strict descent and a large fibre — the object the
  structural branch consumes.  `deployed_branchingControl` instantiates all of this at
  `n = 2²¹`, `k = 2²⁰`, `e = 978944`, `w = 69632`.
* **Scope.**  No `F(n,k,e,s)` bound on the positive-mass branch is claimed or used; at the
  deployed point the a priori child count is astronomically large, so the content of the
  trichotomy is its third branch.  Narrative: `BRANCHING_CONTROL_REPORT.md`.  Axiom audit:
  `RequestProject/BranchingControlAxiomAudit.lean`.

## 138. `MassDescentRecursion`: full recursive child cost, exact multiplicities and the anchor charging of the `τ`-window descent (`RequestProject/Root/CodingTheory/MassDescentRecursion.lean`)

§137 gives the covering recursion `#Bad ≤ (e+1) + Σ_{R ∈ childClasses} C(R)`, closable only by
bounding the number of children.  This section removes the branching factor entirely.

* **Canonical, choice-fixed objects.**  `officialWitness` (a fixed positive-mass official witness
  per challenge, `officialWitness_spec`, `exists_officialWitness_of_mem_posBadSet`),
  `officialClass` (its child class), `classCost R = #Bad(child R)` — the **full recursive** cost —
  `childCost γ`, `parentMult R = μR`, `totalChildCost = Σ_γ childCost γ`.
  `officialClass_determines_child`: equal classes ⇒ literally the same child instance.
  `officialWitness_shortened`, `mem_resBadSet_official`: exact transport (`p = V_Z·r`, `deg r < k₁`,
  residual line point `= r` on the exact residual support, challenge bad for the child).
  `officialClass_capacity_gap` (`n₁ = k₁+e₁+w`), `officialClass_complexity_lt`
  (`e₁ < e`, `k₁+e₁ < k+e`).
* **Exact multiplicity, no double counting.**  `card_posBadSet_eq_sum_parentMult`: `#Bad⁺ = Σ_R μR`;
  `totalChildCost_eq_sum_parentMult`: `totalChildCost = Σ_R μR·C(R)`; `fibre_subset_resBadSet` and
  `parentMult_le_classCost`: `μR ≤ C(R)`.  Hence
  `card_badSet_le_terminal_add_totalChildCost`: `#Bad ≤ (e+1) + Σ_R μR·C(R)` — strictly stronger
  than bounding `Σ_R μR`.
* **The anchor charging.**  With an anchor challenge `γ₀` of window mass `0` and support `S0`
  (`|S0| ≥ t`), the charge set `D_γ = (S_γ ∖ A) ∖ S0` satisfies `|D_γ| ≥ w − s`
  (`card_chargeSet_ge`, from `card_sdiff_window_ge` and the exact challenge transport against a
  zero-mass anchor), and lies in `univ ∖ S0`, of size `≤ e`.  Weighting each challenge by its full
  recursive child cost and double counting (`sum_chargeLoad_eq`) gives
  `massDescent_charging`: `(w−s)·Σ_R μR·C(R) ≤ Σ_{i ∉ S0} load(i)`, hence
  `massDescent_load_bound`: `(w−s)·Σ_R μR·C(R) ≤ e·M` under any uniform load bound `M`, and the
  closed forms `card_badSet_le_of_load_bound`: `(w−s)·(#Bad − (e+1)) ≤ e·M` and
  `card_badSet_le_potential`: `#Bad ≤ Φ = (e+1) + e·M/(w−s)`.
* **Amortisation framework.**  `cost_le_potential`: on any state space with a well-founded
  complexity, a potential with `localCost X + Σ_Y mult X Y·Φ Y ≤ Φ X` dominates a cost with
  `cost X ≤ localCost X + Σ_Y mult X Y·cost Y`.
* **The exact remaining obstruction.**  `exists_concentrated_coordinate` (unconditional, for
  `0 < w−s`): either `#Bad ≤ e+1`, or some single coordinate outside the anchor support carries a
  `(w−s)/e` fraction of the entire recursive cost.  The recursion is summable exactly when the
  per-coordinate recursive load is bounded away from the total; since `load(i) ≤ totalChildCost`
  holds trivially, progress requires a *spread* statement for the official supports, not counting.
  `massDescent_master` packages decomposition, recursion, charging and dichotomy.
* **Deployed.**  `deployed_massDescent`: `69632·(#Bad − 978945) ≤ 978944·M`;
  `deployed_massDescent_budget`: `M ≤ 19·10¹⁵ ⇒ #Bad ≤ B* = 274980728111395087`.  The forced
  concentration fraction is `69632/978944 = 1/14.06`.
* **Scope.**  The closed bounds are conditional on the load bound, stated as an explicit
  hypothesis; `#children × max child cost` is never used and `e` is not assumed to drop by `w`.
  Narrative: `MASS_DESCENT_RECURSION_REPORT.md`.  Axiom audit:
  `RequestProject/MassDescentRecursionAxiomAudit.lean`.

## Official split-locator circuits of arity four — up to the deployed row

* **Route (i) refuted.**  `Root.CodingTheory.OfficialCircuit.official_arity_four_circuit`: split
  locator structure does *not* forbid circuits of arity above three.  For every width `w ≥ 2` and
  every locator degree `e`, a three-class divided-difference word plus the class equation
  `(γ i − r (cls x))·Q_i(x) = θ i·κ x` on a set `T` of `w+1` points yields two official words and
  four distinct official challenges whose joint syndrome vectors are dependent with all four
  coefficients nonzero and with no three of them dependent.
* **Small model.**  `Example13.official_arity_four_circuit_example`: an explicit instance over
  `𝔽₁₃` with `D = μ₁₂`, `n = 12`, `k = 5`, `e = 4`, `w = 3`.
* **Transfer.**  `official_arity_four_circuit_of_labels`: choosing the erasure sets as a common
  part plus full fibres of the `d`-th power map collapses the `w+1` conditions of the class
  equation to `12` label equations, independent of `w`, `e`, the domain size and the field.
  Solvability of those `12` equations is equivalent to four points of `F²` being collinear with
  `(1,1)` on a non-axis-parallel line — a coincidence of the single invariant
  `σ = (b₃−1)/(b₂−1)`.
* **Deployed row reached.**  `Deployed.official_arity_four_circuit_deployed`: an official
  arity-four circuit over `D = μ_{2²¹} ⊂ 𝔽_p`, `p = 2³¹−2²⁴+1`, with `k = 2²⁰`, `e = 978944`,
  `w = 69632`, four monic degree-`e` locators dividing `X^{2097152} − 1`.  The challenges lie in
  the prime subfield; the deployed protocol samples from `𝔽_{p⁶}`.
* **Route (iii).**  `pencil_family_card_le_three`: for the pencil-shaped families the mechanism
  produces, a family with no nonzero challenge-compatible dependency has at most `3` members —
  at the deployed row this improves the dependency-free bound from `69632` to `3`.  So arity four
  coexists with a rank-three, hence tiny, challenge count.
* **Scope.**  No Grand MCA claim is made.  Narrative and full claim ledger:
  `OFFICIAL_CIRCUIT_ARITY_REPORT.md`.  Axiom audits:
  `RequestProject/OfficialCircuitArityAxiomAudit.lean`,
  `RequestProject/OfficialCircuitDeployedAxiomAudit.lean`.
