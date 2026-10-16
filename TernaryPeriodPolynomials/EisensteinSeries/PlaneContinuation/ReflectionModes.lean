module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LadderAdmissibility

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.OrbitSmooth TernaryPeriodPolynomials.PlaneEisensteinContinuation.StageTranslation TernaryPeriodPolynomials.PlaneEisensteinContinuation.DirectionalRealization
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.AnalyticDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieDifferentiation TernaryPeriodPolynomials.PlaneEisensteinContinuation.LieOperators
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.FiniteRotationTypes TernaryPeriodPolynomials.PlaneEisensteinContinuation.LadderAdmissibility
open scoped Matrix.Norms.Elementwise

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes

def reflection : BinaryRealGL :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext row column
    fin_cases row <;> fin_cases column <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem reflection_mul_self : reflection * reflection = 1 := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;> norm_num [reflection, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjugation_reflection_rotation : conjugation reflection rotationMatrix = (-1 : ℝ) • rotationMatrix := by
  rw [conjugation_apply]
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [reflection, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two]

theorem reflection_involutive (data : CuspidalRepresentation) :
    Function.Involutive (smoothTranslate data reflection) := by
  intro vector
  apply Subtype.ext
  change data.π (atInfinity reflection) (data.π (atInfinity reflection) vector.val) = vector.val
  rw [← Module.End.mul_apply, ← map_mul, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Height.atInfinity_mul,
    reflection_mul_self, TernaryPeriodPolynomials.PlaneEisensteinContinuation.AveragingSmooth.atInfinity_one, map_one, Module.End.one_apply]

theorem reflection_eigen (data : CuspidalRepresentation) (vector : data.smooth) (index : ℤ)
    (eigen : rotationOperator data vector = (Complex.I * index) • vector) :
    rotationOperator data (smoothTranslate data reflection vector) =
      (Complex.I * (-index : ℤ)) • smoothTranslate data reflection vector := by
  have equality := directionalOperator_translate data reflection vector rotationMatrix
  rw [conjugation_reflection_rotation, directionalOperator_real_smul] at equality
  change rotationOperator data (smoothTranslate data reflection vector) =
    smoothTranslate data reflection (((-1 : ℝ) : ℂ) • rotationOperator data vector) at equality
  rw [eigen, map_smul, map_smul, smul_smul] at equality
  simpa only [Complex.ofReal_neg, Complex.ofReal_one, Int.cast_neg, neg_one_mul, mul_neg] using equality

theorem reflection_mem_fixedMode (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (vector : data.smooth) (index : ℤ) (membership : vector ∈ fixedMode data level index) :
    smoothTranslate data reflection vector ∈ fixedMode data level (-index) := by
  rw [mem_fixedMode_iff] at membership ⊢
  refine ⟨TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.fixedSubspace_real_stable data level reflection vector.val membership.1, ?_⟩
  exact (rotation_eigen_iff data _ _).mp
    (reflection_eigen data vector index ((rotation_eigen_iff data vector index).mpr membership.2))

noncomputable def reflectionMap (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (index : ℤ) :
    fixedMode data level index →ₗ[ℂ] fixedMode data level (-index) :=
  ((smoothTranslate data reflection).comp (fixedMode data level index).subtype).codRestrict
    (fixedMode data level (-index)) (fun vector => reflection_mem_fixedMode data level vector.val index vector.property)

theorem reflectionMap_injective (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (index : ℤ) :
    Function.Injective (reflectionMap data level index) := by
  intro first second equality
  apply Subtype.ext
  apply (reflection_involutive data).injective
  exact congrArg Subtype.val equality

theorem finiteDimensional_of_neg (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL) (index : ℤ)
    [FiniteDimensional ℂ (fixedMode data level (-index))] : FiniteDimensional ℂ (fixedMode data level index) :=
  FiniteDimensional.of_injective (reflectionMap data level index) (reflectionMap_injective data level index)

theorem finite_types_of_lowest_weight (data : CuspidalRepresentation) (level : Subgroup BinaryFiniteGL)
    (base : ℤ) (baseBound : 3 ≤ base) (vector : data.smooth) (nonzero : vector ≠ 0)
    (rotationEigen : rotationOperator data vector = (Complex.I * base) • vector)
    (lowest : lowering data vector = 0)
    [FiniteDimensional ℂ (fixedMode data level base)] :
    ∀ index : ℤ, FiniteDimensional ℂ (fixedMode data level index) := by
  let _ : FiniteDimensional ℂ (fixedMode data level (- -base)) := by
    rw [neg_neg]
    infer_instance
  let _ : FiniteDimensional ℂ (fixedMode data level (-base)) := finiteDimensional_of_neg data level (-base)
  exact finite_types_of_endpoints data level base baseBound
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirIrreducibility.casimir_scalar_of_eigenvector data _ vector nonzero
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CasimirNorms.lowest_weight_casimir data vector base rotationEigen lowest))

theorem hasSum_of_lowest_weight {degree : ℕ} {data : InducingData degree}
    {sectionFamily : ℂ → AdelicGL → ℂ} (flatSection : IsFlatSection data sectionFamily)
    (base : ℤ) (baseBound : 3 ≤ base) (vector : data.cusp.smooth) (nonzero : vector ≠ 0)
    (rotationEigen : rotationOperator data.cusp vector = (Complex.I * base) • vector)
    (lowest : lowering data.cusp vector = 0)
    [FiniteDimensional ℂ (fixedMode data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence base)]
    (basePoint : AdelicGL) (parameter : ℂ) (rightHalfPlane : -(degree : ℝ) / 2 < parameter.re) :
    HasSum (eisensteinSummand sectionFamily parameter basePoint)
      (TernaryPeriodPolynomials.PlaneEisensteinContinuation.ScalarSeries.literalSum sectionFamily parameter basePoint) :=
  hasSum_of_finite_types flatSection
    (finite_types_of_lowest_weight data.cusp TernaryPeriodPolynomials.PlaneEisensteinContinuation.BinaryLevel.finiteCongruence base baseBound
      vector nonzero rotationEigen lowest) basePoint parameter rightHalfPlane

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.ReflectionModes
