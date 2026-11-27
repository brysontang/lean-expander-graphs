# Expander graphs in Lean 4

A formalization of the foundations of expander graphs and high-dimensional expanders, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). Mathlib had no expander material, so
the definitions and theorems here are new.

## What is proved

| Result | Statement | File |
|---|---|---|
| Largest eigenvalue | A `d`-regular graph has largest adjacency eigenvalue `d`; all eigenvalues lie in `[-d, d]` | `Expanders/Basic.lean` |
| Courant–Fischer for `λ₂` | `λ₂ = max xᵀAx / xᵀx` over `x` orthogonal to constants | `Expanders/SymmetricSpectrum.lean`, `Expanders/Basic.lean` |
| Cheeger's inequality | `(d − λ₂)/2 ≤ h(G) ≤ √(2d(d − λ₂))` | `Expanders/Cheeger.lean` |
| Alon–Boppana bound | Large `d`-regular graphs have `λ₂ ≥ 2√(d−1) − ε` | `Expanders/AlonBoppana.lean` |
| Trickling down (Oppenheim) | Expansion of the smallest links of a pure, connected complex forces expansion of every link | `Expanders/HighDim.lean`, `Expanders/TricklingDownSpectral.lean` |

## What is open

One statement is stated but not proved: *almost every `d`-regular graph is an expander*
(`SimpleGraph.tendsto_regularExpanderFraction` in `Expanders/Existence.lean`). The corollary that
expander families exist is proved from it, so it is open too. These are the only uses of `sorry`.

## Definitions

- **Edge expansion**: `SimpleGraph.edgeBoundary`, the Cheeger constant `SimpleGraph.edgeExpansion`,
  and `SimpleGraph.IsEdgeExpander`.
- **Spectral expansion**: `SimpleGraph.adjEigenvalues`, `SimpleGraph.spectralGap`,
  `SimpleGraph.IsSpectralExpander`, `SimpleGraph.IsRamanujan`.
- **High-dimensional expanders**: links of Mathlib's `PreAbstractSimplicialComplex`, purity,
  connectivity, the weighted graph of a link, and `IsLocalSpectralExpander` (every link has small
  second eigenvalue). Expansion is one-sided throughout: only the second-largest eigenvalue is
  bounded.
- **Weighted graphs**: `WalkSecondEigenvalueLE`, the second eigenvalue of the random walk in
  variational form, used because links are weighted and not regular.

## Build and verify

```
lake exe cache get   # download the Mathlib build cache
lake build
lake env lean Audit.lean
```

`Audit.lean` is a checked list. It fails if any theorem listed as proved depends on `sorry` or on
anything beyond Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and it
fails if a theorem listed as open has been proved without the list being updated. CI runs the
build and the audit on every push.

Requires Lean 4.33.1 and Mathlib `v4.33.1`, pinned in `lean-toolchain` and `lake-manifest.json`.

## Provenance

The Lean code was written with Claude (Anthropic) and checked by the Lean kernel. The theorem
statements are the part a reader should scrutinise: the kernel guarantees each proof matches its
statement, not that the statement says what was intended.

## License

Apache 2.0. See `LICENSE`.
