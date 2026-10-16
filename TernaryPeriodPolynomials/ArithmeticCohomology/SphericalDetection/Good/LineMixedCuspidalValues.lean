module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineCuspidalIntegral

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

def goodLineMixedCuspidalValues {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (base : AdelicGL) :
    cuspidalTensorValues data.cusp (Binary.HomogeneousPoly (degree + 1)) :=
  cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 0)
    (sourcePlaneCuspidalValues data source cocycle
      (goodLineRealVertices (goodLineLeviSection matrix,
        goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeFirst))) base -
      sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineRadicalInclusion radicalLatticeFirst, goodLineLeviSection matrix)) base) +
  cuspidalTensorMap data.cusp (lowerRadicalLatticeContribution degree 1)
    (sourcePlaneCuspidalValues data source cocycle
      (goodLineRealVertices (goodLineLeviSection matrix,
        goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeSecond))) base -
      sourcePlaneCuspidalValues data source cocycle
        (goodLineRealVertices (goodLineRadicalInclusion radicalLatticeSecond, goodLineLeviSection matrix)) base)

theorem goodLineMixedCuspidalValues_apply {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (base : AdelicGL) (argument : BinaryAdelicGL) :
    (goodLineMixedCuspidalValues data source cocycle matrix base).val argument =
      goodLineMixedRealCoordinate degree matrix (fun vertices =>
        (sourcePlaneCuspidalValues data source cocycle vertices base).val argument) := by
  rw [goodLineMixedRealCoordinate_contributions]
  rfl

theorem goodLineMixedCuspidalValues_finiteLevel {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (real : RealGL3) :
    goodLineMixedCuspidalValues data source cocycle matrix (atInfinity real) ∈
      cuspidalTensorFiniteLevel data.cusp (Binary.HomogeneousPoly (degree + 1)) := by
  intro integral argument
  rw [goodLineMixedCuspidalValues_apply, goodLineMixedCuspidalValues_apply]
  apply congrArg (goodLineMixedRealCoordinate degree matrix)
  funext vertices
  exact sourcePlaneCuspidalValues_finiteLevel data source cocycle vertices real integral argument

theorem goodLineMixedCuspidalValues_bounded {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (base : AdelicGL)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    ∃ bound : ℝ, ∀ argument : BinaryAdelicGL,
      ‖functional ((goodLineMixedCuspidalValues data source cocycle matrix base).val argument)‖ ≤ bound := by
  obtain ⟨bound, bounded⟩ := data.cusp.bounded
    (cuspidalTensorFunctional data.cusp functional (goodLineMixedCuspidalValues data source cocycle matrix base))
  refine ⟨bound, ?_⟩
  intro argument
  simpa only [cuspidalTensorFunctional_realize] using bounded argument

theorem cuspidalTensorFunctional_spherical {V : Type} [AddCommGroup V] [Module ℂ V]
    (cusp : CuspidalRepresentation) (functional : V →ₗ[ℂ] ℂ) (values : cuspidalTensorValues cusp V)
    (fixed : values ∈ cuspidalTensorFiniteLevel cusp V) :
    (cuspidalTensorFunctional cusp functional values).val ∈ cuspSphericalValues cusp := by
  intro integral
  let vector := cuspidalTensorFunctional cusp functional values
  have equality : (⟨cusp.π (atFinite (GeneralLinearGroup.map integralEmbedding integral)) vector.val,
      cusp.smooth_stable _ vector.val vector.property⟩ : cusp.smooth) = vector := by
    apply cusp.injective
    funext argument
    rw [cusp.equivariant]
    change cusp.realize (cuspidalTensorFunctional cusp functional values)
      (argument * atFinite (GeneralLinearGroup.map integralEmbedding integral)) =
      cusp.realize (cuspidalTensorFunctional cusp functional values) argument
    rw [cuspidalTensorFunctional_realize, cuspidalTensorFunctional_realize, fixed integral argument]
  exact congrArg Subtype.val equality

theorem goodLineMixedCuspidalValues_functional_spherical {degree : ℕ} (data : InducingData degree)
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (real : RealGL3)
    (functional : Binary.HomogeneousPoly (degree + 1) →ₗ[ℂ] ℂ) :
    (cuspidalTensorFunctional data.cusp functional
      (goodLineMixedCuspidalValues data source cocycle matrix (atInfinity real))).val ∈ cuspSphericalValues data.cusp :=
  cuspidalTensorFunctional_spherical data.cusp functional _
    (goodLineMixedCuspidalValues_finiteLevel data source cocycle matrix real)

end TernaryPeriodPolynomials.SphericalDetection.Helpers
