module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.SeedC3
public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.ESFinal

@[expose] public section


/-!
# Eichler–Shimura spanning at every level, and the unconditional spanning clause of Lemma C.3

`eichler_shimura_spanning_gammaN` proves `ESSpan (Γ(N)) n` for every `N > 0`: every parabolic
class of `H¹(Γ(N), Sym^{n+1} ⊗ det⁻¹)` is a combination of holomorphic and antiholomorphic period
classes of cusp forms of weight `n + 3` (`TernaryPeriodPolynomials.Argument.ESFoundations.ESFinal.esSpan_gamma`). Consequently the
spanning statements of `Statements.SeedC3` that were conditional on this proposition hold
unconditionally, both on `ℤ² ⋊ Γ(N)` (`seed_span_gammaN`, `seed_span_iff_gammaN`) and on the
paper's plane group `Γ(N) ∩ P(ℤ)` with radical `Nℤ²` (`seed_gammaP_span`).

Scope: as in `Statements.SeedC3`, these are the algebraic radical-kernel/parabolic-edge statements on
`H²`; the comparison with the paper's mixed cuspidal group `𝒞_P(E)` (all plane cusps, finite
reflections, the face/boundary comparison) is not part of this file.

Written by Claude Opus 5.5.
-/

namespace TernaryPeriodPolynomials.Argument.Statements.EichlerShimura

open TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- **Eichler–Shimura spanning at every principal congruence subgroup `Γ(N)`, `N > 0`.** -/
theorem eichler_shimura_spanning_gammaN (N n : ℕ) (hN : 0 < N) :
    TernaryPeriodPolynomials.Argument.SeedC3S4c.ESSpan (CongruenceSubgroup.Gamma N) n :=
  TernaryPeriodPolynomials.Argument.ESFoundations.ESFinal.esSpan_gamma N n hN

/-- **Lemma C.3, spanning clause on `ℤ² ⋊ Γ(N)` (unconditional).** A class with zero radical
restriction and parabolic Hochschild–Serre edge lies in the span of the seeds. -/
theorem seed_span_gammaN (N n : ℕ) (hN : 0 < N)
    (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma N) n))
    (hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt (CongruenceSubgroup.Gamma N)).inl
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma N) n) y = 0)
    (hpar : TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge (CongruenceSubgroup.Gamma N) n ⟨y, hy⟩ ∈
      TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma N) n) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan (CongruenceSubgroup.Gamma N) n :=
  SeedC3.seed_span_gammaN_of_eichlerShimura N n (eichler_shimura_spanning_gammaN N n hN) y hy hpar

/-- **Lemma C.3, spanning clause as an equivalence on `ℤ² ⋊ Γ(N)` (unconditional).** -/
theorem seed_span_iff_gammaN (N n : ℕ) (hN : 0 < N)
    (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma N) n)) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.seedSpan (CongruenceSubgroup.Gamma N) n ↔
      ∃ hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelExt (CongruenceSubgroup.Gamma N)).inl
        (TernaryPeriodPolynomials.Argument.SeedC3S4c.levelRep (CongruenceSubgroup.Gamma N) n) y = 0,
      TernaryPeriodPolynomials.Argument.SeedC3S4c.levelEdge (CongruenceSubgroup.Gamma N) n ⟨y, hy⟩ ∈
        TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma N) n :=
  SeedC3.seed_span_iff_of_eichlerShimura _ n (eichler_shimura_spanning_gammaN N n hN) y

/-- **Lemma C.3, spanning clause on the paper's plane group `Γ(N) ∩ P(ℤ)` (radical `Nℤ²`),
unconditional.** -/
theorem seed_gammaP_span (N n : ℕ) [NeZero N]
    (y : groupCohomology.H2 (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRep N n))
    (hy : twoCohomologyRestriction (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNExt N).inl
      (TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNRep N n) y = 0)
    (hpar : TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNEdge N n ⟨y, hy⟩ ∈
      TernaryPeriodPolynomials.Argument.SeedC3S4c.parabolicH1 (CongruenceSubgroup.Gamma N) n) :
    y ∈ TernaryPeriodPolynomials.Argument.SeedC3S4c.gammaNSeedSpan N n :=
  SeedC3.seed_gammaP_span_conditional N n
    (eichler_shimura_spanning_gammaN N n (Nat.pos_of_ne_zero (NeZero.ne N))) y hy hpar

end TernaryPeriodPolynomials.Argument.Statements.EichlerShimura
