module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.UpperBoundaryPotential

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {index : Type} [Fintype index]

theorem realUpperBoundaryPotential_hilbert
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (cycle : groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) :
    cuspidalTensorHilbertEmbedding cusp basis (realUpperBoundaryPotential degree cusp cycle) =
      cuspidalTensorHilbertMap cusp basis basis
          ((upperLatticeBoundaryInverse degree).comp (LinearMap.inl ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))
          (cuspidalTensorHilbertEmbedding cusp basis (cycle (radicalLatticeReal radicalLatticeFirst))) +
        cuspidalTensorHilbertMap cusp basis basis
          ((upperLatticeBoundaryInverse degree).comp (LinearMap.inr ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))
          (cuspidalTensorHilbertEmbedding cusp basis (cycle (radicalLatticeReal radicalLatticeSecond))) := by
  rw [realUpperBoundaryPotential, map_add]
  exact congrArg₂ (fun first second : index → cusp.H => first + second)
    (cuspidalTensorHilbertMap_embedding cusp basis basis _ _).symm
    (cuspidalTensorHilbertMap_embedding cusp basis basis _ _).symm

theorem realUpperBoundaryPotential_contDiff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {order : WithTop ℕ∞}
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (family : E → groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp))
    (first : ContDiff ℝ order (fun point => cuspidalTensorHilbertEmbedding cusp basis
      (family point (radicalLatticeReal radicalLatticeFirst))))
    (second : ContDiff ℝ order (fun point => cuspidalTensorHilbertEmbedding cusp basis
      (family point (radicalLatticeReal radicalLatticeSecond)))) :
    ContDiff ℝ order (fun point => cuspidalTensorHilbertEmbedding cusp basis
      (realUpperBoundaryPotential degree cusp (family point))) := by
  simp_rw [realUpperBoundaryPotential_hilbert degree cusp basis]
  exact (((cuspidalTensorHilbertMap cusp basis basis
    ((upperLatticeBoundaryInverse degree).comp (LinearMap.inl ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))).restrictScalars ℝ).contDiff.comp first).add
      (((cuspidalTensorHilbertMap cusp basis basis
    ((upperLatticeBoundaryInverse degree).comp (LinearMap.inr ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))).restrictScalars ℝ).contDiff.comp second)

theorem realUpperBoundaryPotential_analyticAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (degree : ℕ) (cusp : CuspidalRepresentation) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (family : E → groupCohomology.cocycles₁ (realUpperCuspidalRep degree cusp)) (point : E)
    (first : AnalyticAt ℝ (fun input => cuspidalTensorHilbertEmbedding cusp basis
      (family input (radicalLatticeReal radicalLatticeFirst))) point)
    (second : AnalyticAt ℝ (fun input => cuspidalTensorHilbertEmbedding cusp basis
      (family input (radicalLatticeReal radicalLatticeSecond))) point) :
    AnalyticAt ℝ (fun input => cuspidalTensorHilbertEmbedding cusp basis
      (realUpperBoundaryPotential degree cusp (family input))) point := by
  simp_rw [realUpperBoundaryPotential_hilbert degree cusp basis]
  exact ((((cuspidalTensorHilbertMap cusp basis basis
    ((upperLatticeBoundaryInverse degree).comp (LinearMap.inl ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))).restrictScalars ℝ).analyticAt _).comp first).add
      ((((cuspidalTensorHilbertMap cusp basis basis
    ((upperLatticeBoundaryInverse degree).comp (LinearMap.inr ℂ (HomogeneousPoly degree) (HomogeneousPoly degree)))).restrictScalars ℝ).analyticAt _).comp second)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
