module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.RelativeRepresentative
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Source.ParabolicRegularity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneMixedPrimitive
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneHilbertAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Real.PlaneLevelForget

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem realRadicalInverseLeviCoordinates_contDiff {order : WithTop ℕ∞} (matrix : BinaryRealGL) :
    ContDiff ℝ order (fun point : Fin 2 → ℝ =>
      (realRadicalInverseLevi matrix (Multiplicative.ofAdd point)).toAdd) := by
  change ContDiff ℝ order (fun point : Fin 2 → ℝ => matrix⁻¹.val.mulVec point)
  apply contDiff_pi.mpr
  intro position
  change ContDiff ℝ order (fun point : Fin 2 → ℝ => ∑ source, matrix⁻¹.val position source * point source)
  apply ContDiff.sum
  intro source _
  exact contDiff_const.mul (contDiff_apply ℝ ℝ source)

theorem sourcePlaneRelative_mixed_hilbertContDiff {degree : ℕ} {index : Type} [Fintype index]
    (data : InducingData degree) (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source)
    (primitive : RealPlaneRadical → realPlaneLevelCuspidalRep degree data.cusp data.chi)
    (regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
      cuspidalTensorHilbertEmbedding data.cusp basis (primitive (Multiplicative.ofAdd point)).val))
    (relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
      (realPlaneLevelCuspidalRep degree data.cusp data.chi))
    (formula : relative.val = sourcePlaneNormalizedGroupCocycle data source cocycle -
      twoBoundaryCycle _ (realPlanePrimitiveExtension _ primitive)) (matrix : BinaryRealGL) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
      cuspidalTensorHilbertEmbedding data.cusp basis
        (relative.val (SemidirectProduct.inr matrix,
          SemidirectProduct.inl (realRadicalInverseLevi matrix (Multiplicative.ofAdd point)))).val -
      cuspidalTensorHilbertEmbedding data.cusp basis
        (relative.val (SemidirectProduct.inl (Multiplicative.ofAdd point), SemidirectProduct.inr matrix)).val) := by
  have unit_zero := realPlaneRelative_primitive_unit _ _
    (sourcePlaneNormalizedGroupCocycle_unit data source cocycle) primitive relative formula
  have inverse_regular : ContDiff ℝ ⊤ (fun point : Fin 2 → ℝ =>
      (realPlaneMatrix (SemidirectProduct.inl (realRadicalInverseLevi matrix (Multiplicative.ofAdd point)))).val) := by
    simp only [realPlaneMatrix_inl]
    convert realPlaneRadicalMatrix_contDiff.comp (realRadicalInverseLeviCoordinates_contDiff matrix) using 1
    rfl
  have radical_regular : ContDiff ℝ ⊤ (fun point : Fin 2 → ℝ =>
      (realPlaneMatrix (SemidirectProduct.inl (Multiplicative.ofAdd point))).val) := by
    simpa only [realPlaneMatrix_inl] using (realPlaneRadicalMatrix_contDiff (order := ⊤))
  have first_regular := (sourcePlaneNormalizedGroupCocycle_hilbertContDiff data basis source cocycle
    (fun _ => SemidirectProduct.inr matrix)
    (fun point : Fin 2 → ℝ => SemidirectProduct.inl (realRadicalInverseLevi matrix (Multiplicative.ofAdd point)))
    contDiff_const inverse_regular).of_le (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ ⊤ from le_top)
  have second_regular := (sourcePlaneNormalizedGroupCocycle_hilbertContDiff data basis source cocycle
    (fun point : Fin 2 → ℝ => SemidirectProduct.inl (Multiplicative.ofAdd point))
    (fun _ => SemidirectProduct.inr matrix) radical_regular contDiff_const).of_le
      (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ ⊤ from le_top)
  have primitive_regular : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
      cuspidalTensorHilbertEmbedding data.cusp basis
        (primitive (realRadicalInverseLevi matrix (Multiplicative.ofAdd point))).val) := by
    convert regular.comp (realRadicalInverseLeviCoordinates_contDiff matrix) using 1
    rfl
  have action_regular := ((realPlaneHilbertOperator degree data.cusp data.chi basis (SemidirectProduct.inr matrix)).restrictScalars ℝ).contDiff.comp primitive_regular
  convert ((first_regular.sub second_regular).sub action_regular).add regular using 1
  funext point
  let embedding : realPlaneLevelCuspidalRep degree data.cusp data.chi →ₗ[ℂ] (index → data.cusp.H) :=
    (cuspidalTensorHilbertEmbedding data.cusp basis).comp
      (cuspidalTensorFiniteLevel data.cusp (HomogeneousPoly degree)).subtype
  have equality := congrArg embedding (realPlaneRelative_mixed_formula _ _ primitive unit_zero relative formula matrix (Multiplicative.ofAdd point))
  simp only [map_sub, map_add] at equality
  change embedding (relative.val _) - embedding (relative.val _) = _
  rw [equality]
  have action : embedding ((realPlaneLevelCuspidalRep degree data.cusp data.chi).ρ (SemidirectProduct.inr matrix)
      (primitive (realRadicalInverseLevi matrix (Multiplicative.ofAdd point)))) =
      realPlaneHilbertOperator degree data.cusp data.chi basis (SemidirectProduct.inr matrix)
        (cuspidalTensorHilbertEmbedding data.cusp basis (primitive (realRadicalInverseLevi matrix (Multiplicative.ofAdd point))).val) :=
    realPlaneHilbertOperator_intertwines degree data.cusp data.chi basis (SemidirectProduct.inr matrix)
      (primitive (realRadicalInverseLevi matrix (Multiplicative.ofAdd point))).val
  rw [action]
  rfl

theorem sourcePlaneLevelGroupCocycle_exists_regular_relative {degree : ℕ} {index : Type} [Fintype index]
    (positive : 0 < degree) (odd : Odd degree) (data : InducingData degree) (trivial : data.chi = trivialCharacter)
    (basis : Module.Basis index ℂ (HomogeneousPoly degree))
    (source : SourceCochain degree) (cocycle : IsSourceCocycle data .plane source) :
    ∃ relative : relativeTwoCocycles (SemidirectProduct.toGroupExtension realPlaneRadicalAction).inl
        (realPlaneLevelCuspidalRep degree data.cusp data.chi),
      groupCohomology.H2π _ relative.val = groupCohomology.H2π _ (sourcePlaneLevelGroupCocycle data source cocycle) ∧
      ∀ matrix : BinaryRealGL, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun point : Fin 2 → ℝ =>
        cuspidalTensorHilbertEmbedding data.cusp basis
          (relative.val (SemidirectProduct.inr matrix,
            SemidirectProduct.inl (realRadicalInverseLevi matrix (Multiplicative.ofAdd point)))).val -
        cuspidalTensorHilbertEmbedding data.cusp basis
          (relative.val (SemidirectProduct.inl (Multiplicative.ofAdd point), SemidirectProduct.inr matrix)).val) := by
  obtain ⟨primitive, regular, relative, formula, same_class⟩ :=
    sourcePlaneLevelGroupCocycle_exists_relative positive odd data trivial basis source cocycle
  exact ⟨relative, same_class, sourcePlaneRelative_mixed_hilbertContDiff data basis source cocycle primitive regular relative formula⟩

end TernaryPeriodPolynomials.SphericalDetection.Helpers
