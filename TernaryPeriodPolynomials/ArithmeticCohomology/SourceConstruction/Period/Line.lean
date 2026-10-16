module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Period.Sign
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.SourceData

@[expose] public section


/-!
# Line Levi cocycle data from the sign-twisted Eichler cocycle

A sign-twisted Eichler cocycle (`IsSignEichlerCocycle`) is exactly a `LineLeviCocycleData`: the
sign `signDet` of the twisted cocycle law and `lineSgn` of the line source construction are the same
function.  The data built from the Hecke-eigenvector Eichler input has nonzero arithmetic period class
in `H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) 0)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.TwistedSource

/-- A sign-twisted Eichler cocycle, packaged as line Levi cocycle data. -/
def LineLeviCocycleData.ofSignEichler {σ : CuspidalRepresentation} {n : ℕ}
    {α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (h : IsSignEichlerCocycle σ n α) : LineLeviCocycleData σ n where
  α := α
  cocycle := h.1
  orth := h.2.1
  lift μ g := Classical.choose (h.2.2.2.1 μ) g
  lift_realize μ g A := (Classical.choose_spec (h.2.2.2.1 μ)).2.1 g A
  lift_smooth μ := (Classical.choose_spec (h.2.2.2.1 μ)).1
  scalar_smooth μ A := h.2.2.2.2.1 A μ
  spherical μ g := (Classical.choose_spec (h.2.2.2.1 μ)).2.2 g

theorem LineLeviCocycleData.ofSignEichler_α {σ : CuspidalRepresentation} {n : ℕ}
    {α : BinaryRealGL → BinaryAdelicGL → Binary.HomogeneousPoly (n + 1)}
    (h : IsSignEichlerCocycle σ n α) : (LineLeviCocycleData.ofSignEichler h).α = α := rfl

/-- **Line Levi cocycle data with a nonzero arithmetic period class.** -/
theorem exists_lineLeviCocycleData_period_ne_zero {n : ℕ} (D : InducingData n)
    (spherical : SphericalCusp D.cusp) (odd : Odd n) :
    ∃ (E : LineLeviCocycleData D.cusp n)
      (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0)),
      (∀ m : GeneralLinearGroup (Fin 2) ℤ,
        φ m = E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1) ∧
      groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0 := by
  obtain ⟨α, hα, φ, hφ, nonzero⟩ :=
    exists_isSignEichlerCocycle_period_ne_zero_of_inducing D spherical odd
  exact ⟨LineLeviCocycleData.ofSignEichler hα, φ, hφ, nonzero⟩

end TernaryPeriodPolynomials.SourceConstruction

end
