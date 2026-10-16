module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.SeedInjective

@[expose] public section


/-!
# Eichler-Shimura injectivity at level `Γ(N)` (seed map) and canonicity of the line constant term

Paper: "Eichler-Shimura theory" and `ar:eq:constantterms`.

* `seedMapInjective`: the seed map `f ↦ seedBoundary f` (holomorphic seed of `f x false` plus antiholomorphic seed of `f x true`, at every plane face) has trivial kernel
  on tuples of cusp forms of `Γ₂(N)`, i.e. `S_{n+3}(Γ(N)) ⊕ \bar S_{n+3}(Γ(N)) → H¹_par(Γ(N), Sym^{n+1} ⊗ det⁻¹)` is injective, face by face.  Proved for every `N ≠ 0`
  and every `n` by Green's formula (Petersson/Haberland) on a truncated fundamental domain of `SL₂(ℤ)`; no Hecke operators, no dimension formula.
* `classicalLine`: `ClassicalLineConstantTerm N n hn` (`r_Q ℰ_P(ξ) = Tξ` with one linear `T`, for every presentation of `ξ`) for `3 ≤ N`, `4 ≤ n`.  It does NOT use
  Proposition C.5 at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EichlerShimuraInjective

open TernaryPeriodPolynomials.Argument.FormClassK

/-- **Eichler-Shimura injectivity at `Γ(N)`**: the seed map is injective. -/
theorem seedMapInjective (N : ℕ) [NeZero N] (n : ℕ) : SeedMapInjective N n :=
  TernaryPeriodPolynomials.Argument.EichlerShimuraInj.seedMapInjective N n

/-- **Canonicity of the line constant term**, unconditionally in the seed map. -/
theorem classicalLine (N : ℕ) [NeZero N] (n : ℕ) (hN : 3 ≤ N) (hn : 4 ≤ n) :
    ClassicalLineConstantTerm N n hn :=
  TernaryPeriodPolynomials.Argument.EichlerShimuraInj.classicalLine N n hN hn

end TernaryPeriodPolynomials.Argument.Statements.EichlerShimuraInjective
