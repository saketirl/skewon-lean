# Skewon: Machine-Checked Verification in Lean 4

A self-contained, machine-checked verification (core Lean 4, **no Mathlib, no `sorry`, no `native_decide`**) of the algebraic results in:

> Solonko, Molozhavenko, Rakhuba,
> **"Muon on the Stiefel Manifold Admits an Exact Closed-Form Update"**
> [arXiv:2608.06218](https://arxiv.org/abs/2608.06218)

The paper gives an exact closed-form solution to the linear minimization oracle behind Muon on the Stiefel manifold ("Skewon"): the optimal skew-symmetric step is `Y* = −msign(skew(M Xᵀ))`, computable with matrix multiplies and `msign` only — no dual-ascent inner loop and no matrix inverses.

## Contents

- [`SkewonSymbolic.lean`](SkewonSymbolic.lean) — every theorem is **universally quantified**: over all dimensions `n, p`, all `X ∈ St(n,p)`, all skew-symmetric `Y`, and all gradient directions `M`. Pure structural proofs from first principles (finite sums over `Fin n`, a verified matrix-algebra lemma library, block matrices).

## What is proven (fully general)

- **§2 feasibility**: `Y` skew ⟹ `Y·X ∈ T_X St(n,p)`
- **§2 objective equivalence** (4)↔(5)↔(6): `⟨skew(MXᵀ), Y⟩ = ⟨M, YX⟩` for skew `Y`; the objective sees only the skew part of `Y`
- **Theorem 1** (direct sum `𝒜ⁿ = L_X ⊕ K_X`), all algebraic claims: the explicit decomposition `Y = Ỹ + Y_ker` (Eqs. 8–9), `Y_ker·X = 0`, `Ỹ·X = Y·X`, both components skew, Frobenius orthogonality `⟨Ỹ, Y_ker⟩ = 0`, and the dimension count
- **Proposition 2** (boundary witness): tangency and self-adjointness of the projection `P_X`, `⟨M, P_X M⟩ ≥ 0`, witness objective ≤ 0
- **Algorithm 2 / Eq. (13)**: the low-rank factorization `[−X M]·J·[−X M]ᵀ = 2·skew(MXᵀ)` behind the efficient `p ≪ n` implementation

Statements clear the factor ½ and use integer entries; every proof uses only commutative-ring reasoning, so each identity is valid verbatim over ℝ.

**Not covered symbolically** (needs SVD existence / spectral analysis, i.e. Mathlib-level real analysis): Proposition 1's closed form and optimal value `−‖N‖₊`, Theorem 2's Davis–Kahan–Weinberger completion, Proposition 4, Theorem 3's convergence. The algebraic skeleton these rest on is what is verified here.

## Running

```bash
lean SkewonSymbolic.lean   # Lean ≥ 4.15, core only — no dependencies
```

Compiles in ~3 s. The axiom audit at the end of the file confirms every theorem depends only on Lean's standard foundational axioms (`propext`, `Quot.sound`, and `Classical.choice` in one proof via a decidability instance) — no compiler trust (`ofReduceBool`) anywhere.
