module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

local instance threeLevelPlaceDecidableEq : DecidableEq FinitePlace := Classical.decEq _

theorem integralThree_single (value : ℤ_[3]) :
    integralThree (Pi.single placeThree (threeIntegralEquiv.symm value)) = value := by
  simp [integralThree]

theorem finiteAtThreeScalar_integral (value : ℤ_[3]) :
    finiteAtThreeScalar (value : ℚ_[3]) ∈ Set.range integralEmbedding := by
  refine ⟨Pi.single placeThree (threeIntegralEquiv.symm value), ?_⟩
  apply finiteAdeles_eq_of_three_and_away
  · rw [finiteThree_integral, integralThree_single, finiteAtThreeScalar_three]
  · intro place away
    rw [integralEmbedding_at, Pi.single_eq_of_ne away, finiteAtThreeScalar_away _ place away]
    rfl

theorem finiteAtThreeMatrix_integral (matrix : Matrix (Fin 3) (Fin 3) ℤ_[3]) (row column : Fin 3) :
    finiteAtThreeMatrix (padicThreeEmbedding.mapMatrix matrix) row column ∈ Set.range integralEmbedding := by
  change (1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) row column +
    finiteAtThreeScalar (padicThreeEmbedding (matrix row column) -
      finiteThree ((1 : Matrix (Fin 3) (Fin 3) FiniteAdeles) row column)) ∈ _
  apply integralEmbedding.range.add_mem
  · by_cases same : row = column
    · simpa only [Matrix.one_apply, ite_eq_left same] using integralEmbedding.range.one_mem
    · simpa only [Matrix.one_apply, ite_eq_right same] using integralEmbedding.range.zero_mem
  · by_cases same : row = column
    · rw [Matrix.one_apply, ite_eq_left same, map_one, ← map_one padicThreeEmbedding,
        ← map_sub, padicThreeEmbedding_apply]
      exact finiteAtThreeScalar_integral _
    · rw [Matrix.one_apply, ite_eq_right same, map_zero, sub_zero, padicThreeEmbedding_apply]
      exact finiteAtThreeScalar_integral _

theorem finiteAtThree_integral (matrix : GeneralLinearGroup (Fin 3) ℤ_[3]) :
    finiteAtThree (GeneralLinearGroup.map padicThreeEmbedding matrix) ∈ finiteIntegralGLLevel 3 := by
  apply (finiteIntegralGLLevel_mem_iff _).mpr
  constructor
  · intro row column
    exact finiteAtThreeMatrix_integral matrix.val row column
  · intro row column
    rw [← map_inv, ← map_inv]
    exact finiteAtThreeMatrix_integral matrix⁻¹.val row column

theorem generalLinearGroup_map_injective {source target : Type*} [CommRing source] [CommRing target]
    (hom : source →+* target) (injective : Function.Injective hom) :
    Function.Injective (GeneralLinearGroup.map (n := Fin 3) hom) := by
  intro first second equality
  apply Units.ext
  funext row column
  apply injective
  exact congrArg (fun matrix => matrix.val row column) equality

theorem padicThreeEmbedding_injective : Function.Injective padicThreeEmbedding := by
  intro first second equality
  exact Subtype.ext equality

/-- The embedding supported at three carries the literal local level into the exact adelic level. -/
theorem finiteAtThree_level (matrix : LocalThreeGL) (level : InLocalThreeLevel matrix) :
    finiteAtThree matrix ∈ finiteLevel := by
  obtain ⟨integer, fixed, original⟩ := level
  rw [padicThreeEmbedding_matrix] at original
  rw [← original]
  obtain ⟨compact, compact_eq⟩ := finiteAtThree_integral integer
  have at_three : GeneralLinearGroup.map integralThree compact = integer := by
    apply generalLinearGroup_map_injective padicThreeEmbedding padicThreeEmbedding_injective
    rw [finiteThree_integralMatrix, compact_eq, finiteAtThree_three]
  refine ⟨compact, ?_, compact_eq⟩
  change lastRow ᵥ* (GeneralLinearGroup.map integralReduction compact).val = lastRow
  rw [← integralThree_reduceMatrix, at_three]
  exact fixed

end TernaryPeriodPolynomials.SphericalDetection.Helpers
