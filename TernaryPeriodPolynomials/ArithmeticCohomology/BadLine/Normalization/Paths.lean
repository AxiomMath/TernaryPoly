module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Normalization.Geometry

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PolynomialBadLineNormalization.Helpers TernaryPeriodPolynomials.PolynomialBadLineNormalization.Geometry

namespace TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths

theorem levi_mul {first second : RationalGL3}
    (first_levi : IsRationalLevi first) (second_levi : IsRationalLevi second) :
    IsRationalLevi (first * second) := by
  rcases first_levi with ⟨first_one, first_two, first_three, first_four⟩
  rcases second_levi with ⟨second_one, second_two, second_three, second_four⟩
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_three,
      first_one, first_two, second_one]
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_three,
      first_one, first_two, second_two]
  constructor
  · simp [Matrix.mul_apply, Fin.sum_univ_three,
      second_three, second_four, first_three]
  · simp [Matrix.mul_apply, Fin.sum_univ_three,
      second_three, second_four, first_four]

theorem levi_path_boundary (element : rationalLevel) (levi : IsRationalLevi element.val) :
    chainBoundary (connector - translateChain element.val connector) =
      Finsupp.single (translateVertex element.val pathBase) 1 - Finsupp.single pathBase 1 := by
  rw [map_sub, chainBoundary_translate, connector_boundary]
  simp only [map_sub, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    levi_fixes_otherBase element.val levi]
  abel

theorem unipotent_in_level (first second : ℤ) :
    lineUnipotent (first : ℚ) (second : ℚ) ∈ rationalLevel := by
  let integral : IntegralGL3 := lineUnipotent first second
  have integral_mem : integral ∈ arithmeticLevel := by
    change lastRow ᵥ* (reductionThree integral).val = lastRow
    ext column
    fin_cases column <;>
      simp [integral, lastRow, reductionThree, GeneralLinearGroup.map_apply,
        Matrix.vecMul, dotProduct, upperUnipotent,
        Matrix.cons_val_two, Pi.single_apply]
  refine ⟨⟨integral, integral_mem⟩, ?_⟩
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [rationalInclusion, integral, upperUnipotent,
      GeneralLinearGroup.map_apply, Matrix.cons_val_two]

def binaryIntegralA : IntegralGL3 :=
  ⟨!![1,0,0;0,1,-1;0,3,-2], !![1,0,0;0,-2,1;0,-3,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]⟩

def binaryIntegralB : IntegralGL3 :=
  ⟨!![1,0,0;0,-1,0;0,-3,1], !![1,0,0;0,-1,0;0,-3,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]⟩

def binaryIntegralR : IntegralGL3 :=
  ⟨!![1,0,0;0,-1,0;0,0,1], !![1,0,0;0,-1,0;0,0,1], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two], by
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_two]⟩

theorem binary_in_level (element : RationalGL3)
    (binary : element = binaryA ∨ element = binaryB ∨ element = binaryR) :
    element ∈ rationalLevel := by
  rcases binary with rfl | rfl | rfl
  · refine ⟨⟨binaryIntegralA, ?_⟩, ?_⟩
    · change lastRow ᵥ* (reductionThree binaryIntegralA).val = lastRow
      ext column
      fin_cases column <;> decide
    · apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;>
        norm_num [rationalInclusion, binaryIntegralA, binaryA,
          GeneralLinearGroup.map_apply, Matrix.cons_val_two]
  · refine ⟨⟨binaryIntegralB, ?_⟩, ?_⟩
    · change lastRow ᵥ* (reductionThree binaryIntegralB).val = lastRow
      ext column
      fin_cases column <;> decide
    · apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;>
        norm_num [rationalInclusion, binaryIntegralB, binaryB,
          GeneralLinearGroup.map_apply, Matrix.cons_val_two]
  · refine ⟨⟨binaryIntegralR, ?_⟩, ?_⟩
    · change lastRow ᵥ* (reductionThree binaryIntegralR).val = lastRow
      ext column
      fin_cases column <;> decide
    · apply Units.ext
      ext row column
      fin_cases row <;> fin_cases column <;>
        norm_num [rationalInclusion, binaryIntegralR, binaryR,
          GeneralLinearGroup.map_apply, Matrix.cons_val_two]

theorem binary_levi (element : RationalGL3)
    (binary : element = binaryA ∨ element = binaryB ∨ element = binaryR) :
    IsRationalLevi element := by
  rcases binary with rfl | rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem binary_connector_fixed (element : RationalGL3)
    (binary : element = binaryB ∨ element = binaryR) :
    translateChain element connector = connector := by
  have first_fixed : element • (QuotientGroup.mk (weyl * swapFirstTwo) : Edges) =
      QuotientGroup.mk (weyl * swapFirstTwo) := by
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    change Adelic.InPlaneParabolic ((weyl * swapFirstTwo)⁻¹ *
      (element * (weyl * swapFirstTwo))) ∧
      Adelic.InLineParabolic ((weyl * swapFirstTwo)⁻¹ *
        (element * (weyl * swapFirstTwo)))
    rcases binary with rfl | rfl <;>
      repeat' constructor <;>
        norm_num [weyl, swapFirstTwo, binaryB, binaryR, Matrix.mul_apply,
          Fin.sum_univ_three, Matrix.cons_val_two]
  have second_fixed : element • (QuotientGroup.mk (weyl ^ 2) : Edges) =
      QuotientGroup.mk (weyl ^ 2) := by
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    change Adelic.InPlaneParabolic ((weyl ^ 2)⁻¹ * (element * weyl ^ 2)) ∧
      Adelic.InLineParabolic ((weyl ^ 2)⁻¹ * (element * weyl ^ 2))
    rcases binary with rfl | rfl <;>
      repeat' constructor <;>
        norm_num [pow_two, weyl, binaryB, binaryR, Matrix.mul_apply,
          Fin.sum_univ_three, Matrix.cons_val_two]
  simp only [connector, map_sub, translateChain_single, first_fixed, second_fixed]

noncomputable def normalizedPaths (original : rationalLevel → EdgeChains)
    (element : rationalLevel) : EdgeChains := by
  classical
  exact if IsRationalLevi element.val then connector - translateChain element.val connector
    else if IsRationalRadical element.val then 0
    else original element

theorem normalizedPaths_levi (original : rationalLevel → EdgeChains)
    (element : rationalLevel) (levi : IsRationalLevi element.val) :
    normalizedPaths original element = connector - translateChain element.val connector := by
  simp [normalizedPaths, levi]

theorem normalizedPaths_radical (original : rationalLevel → EdgeChains)
    (element : rationalLevel) (radical : IsRationalRadical element.val) :
    normalizedPaths original element = 0 := by
  classical
  rcases radical with ⟨first, second, equation⟩
  by_cases levi : IsRationalLevi element.val
  · have first_zero : first = 0 := by
      simpa [equation, upperUnipotent] using levi.1
    have second_zero : second = 0 := by
      simpa [equation, upperUnipotent, Matrix.cons_val_two] using levi.2.1
    have identity : element.val = 1 := by
      rw [equation, first_zero, second_zero]
      exact (lineUnipotentHom ℚ).map_one
    rw [normalizedPaths_levi original element levi, identity, translateChain_one, sub_self]
  · have not_levi : ¬IsRationalLevi (lineUnipotent first second) := by
      simpa only [equation] using levi
    simp [normalizedPaths, IsRationalRadical, equation, not_levi]

theorem normalizedPaths_isPathFamily (original : rationalLevel → EdgeChains)
    (original_paths : IsPathFamily original) : IsPathFamily (normalizedPaths original) := by
  classical
  intro element
  by_cases levi : IsRationalLevi element.val
  · rw [normalizedPaths_levi original element levi]
    exact ⟨goodChain_sub connector_good (goodChain_translate element connector_good),
      levi_path_boundary element levi⟩
  · by_cases radical : IsRationalRadical element.val
    · rw [normalizedPaths_radical original element radical]
      refine ⟨goodChain_zero, ?_⟩
      rcases radical with ⟨first, second, equation⟩
      rw [equation, radical_fixes_base, sub_self, map_zero]
    · simpa only [normalizedPaths, ite_eq_right levi, ite_eq_right radical] using original_paths element

theorem integral_levi (element : IntegralGL3) (levi : BadLineLevi element) :
    IsRationalLevi (GeneralLinearGroup.map (Int.castRingHom ℚ) element) := by
  rcases levi with ⟨_, first, second, third, fourth⟩
  simp [IsRationalLevi, GeneralLinearGroup.map_apply, first, second, third, fourth]

theorem integral_in_level (element : IntegralGL3) (membership : element ∈ arithmeticLevel) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) element ∈ rationalLevel :=
  ⟨⟨element, membership⟩, rfl⟩

end TernaryPeriodPolynomials.PolynomialBadLineNormalization.Paths
