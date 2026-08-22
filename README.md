# Skewon: Machine-Checked Verification in Lean 4

Self-contained, machine-checked verifications (core Lean 4, **no Mathlib, no `sorry`**) of the results in:

> Solonko, Molozhavenko, Rakhuba,
> **"Muon on the Stiefel Manifold Admits an Exact Closed-Form Update"**
> [arXiv:2608.06218](https://arxiv.org/abs/2608.06218)

— and of two analogs of its Theorem 1 for constraint sets beyond the Stiefel manifold: **Gram-preserving** optimization of a general weight matrix (orbit W ← R·W), and **composition-preserving** optimization of factored maps P = A·B (two-sided orbit), as used for attention pairs W_qᵀW_k and W_o·W_v.

## Files

| File | Style | Content |
|---|---|---|
| [`SkewonSymbolic.lean`](SkewonSymbolic.lean) | symbolic | §2 setup + Theorem 1 of the paper, fully general (superseded by the file below) |
| [`SkewonThm1Thm2.lean`](SkewonThm1Thm2.lean) | symbolic | **Theorems 1 and 2** of the paper. Theorem 1 unconditional; Theorem 2 (Equivalence of Optima) proven relative to three named analytic hypotheses — unitary invariance of ‖·‖₂ (×2) and the Davis–Kahan–Weinberger completion (the paper's Prop 3) — with everything the paper's proof argues (block construction, skewness, norm bookkeeping, Y·X = B, value equivalence) proven by kernel-checked ring algebra |
| [`GramOrbitThm1.lean`](GramOrbitThm1.lean) | symbolic | **Gram-preserving analog** ("OrbitMuon"): exact Gram preservation under the rotation orbit at a GENERAL (non-orthonormal) W; the LMO over Gram-preserving directions equals the plain Skewon LMO on N = skew(G·Wᵀ) — unconditionally (same witness, no norm facts needed); Theorem 1 direct sum via W = X·H, kernel characterization K_W = K_X, surjectivity {Y·W : Y skew} = {Δ : ΔᵀW + WᵀΔ = 0}, dimension count |
| [`CompSkewonThm1.lean`](CompSkewonThm1.lean) | symbolic | **Composition-preserving analog** ("ComposedSkewon") for P = A·B: factor rotations realize composition orbits with the spectrum of P exactly invariant; **over-rigidity** — the gauge (dA = AX, dB = −XB) preserving P exactly has identically zero objective for any loss factoring through P; the joint LMO separates into two independent Skewon LMOs on N_L = skew(G_P·Pᵀ), N_R = skew(Pᵀ·G_P), whose msign arguments are computable from factor gradients: (G_P·Bᵀ)·Aᵀ = G_P·Pᵀ, Bᵀ·(Aᵀ·G_P) = Pᵀ·G_P |

All symbolic files: every theorem universally quantified over all dimensions and matrices; entries in ℤ with factors of ½ cleared; only commutative-ring reasoning, hence valid verbatim over ℝ. Axiom audits at each file's end show only Lean's standard foundational axioms (`propext`, `Quot.sound`, occasionally `Classical.choice`) — no `native_decide`, no compiler trust.

**What stays outside the symbolic framework** (needs SVD existence / spectral analysis over ℝ): Proposition 1's closed form Y* = −msign(N) with value −‖N‖₊, DKW itself, Proposition 4, convergence. The Gram/composition files are notable in that their problem equivalences need **no** spectral-norm facts at all: the faced and simplified problems share the same feasible generators with pointwise-equal objectives.

## Running

```bash
lean SkewonThm1Thm2.lean     # each file is standalone; Lean >= 4.15, core only
lean GramOrbitThm1.lean
lean CompSkewonThm1.lean
```

Each compiles in ~3 s.
