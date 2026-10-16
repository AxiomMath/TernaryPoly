module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalExtension

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def integralBinaryA : IntegralGL3 :=
  ⟨!![1,0,0;0,1,-1;0,3,-2], !![1,0,0;0,-2,1;0,-3,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def integralBinaryB : IntegralGL3 :=
  ⟨!![1,0,0;0,-1,0;0,-3,1], !![1,0,0;0,-1,0;0,-3,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def integralBinaryR : IntegralGL3 :=
  ⟨!![1,0,0;0,-1,0;0,0,1], !![1,0,0;0,-1,0;0,0,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem integralBinaryA_map :
    GeneralLinearGroup.map (Int.castRingHom ℚ) integralBinaryA = binaryA := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, integralBinaryA, binaryA]

theorem integralBinaryB_map :
    GeneralLinearGroup.map (Int.castRingHom ℚ) integralBinaryB = binaryB := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, integralBinaryB, binaryB]

theorem integralBinaryR_map :
    GeneralLinearGroup.map (Int.castRingHom ℚ) integralBinaryR = binaryR := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, integralBinaryR, binaryR]

theorem integralBinaryA_levi : BadLineLevi integralBinaryA := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [arithmeticLevel_mem_iff]
  intro i
  fin_cases i <;> decide

theorem integralBinaryB_levi : BadLineLevi integralBinaryB := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [arithmeticLevel_mem_iff]
  intro i
  fin_cases i <;> decide

theorem integralBinaryR_levi : BadLineLevi integralBinaryR := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [arithmeticLevel_mem_iff]
  intro i
  fin_cases i <;> decide

theorem binaryA_mem : binaryA ∈ rationalLevel := by
  rw [← integralBinaryA_map]
  exact rationalLevel_badLineLevi integralBinaryA integralBinaryA_levi

theorem binaryB_mem : binaryB ∈ rationalLevel := by
  rw [← integralBinaryB_map]
  exact rationalLevel_badLineLevi integralBinaryB integralBinaryB_levi

theorem binaryR_mem : binaryR ∈ rationalLevel := by
  rw [← integralBinaryR_map]
  exact rationalLevel_badLineLevi integralBinaryR integralBinaryR_levi

theorem binaryA_conjugate (s t : ℚ) :
    binaryA⁻¹ * Adelic.lineUnipotent s t * binaryA =
      Adelic.lineUnipotent (s+3*t) (-s-2*t) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryA, Adelic.lineUnipotent, Adelic.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem binaryB_conjugate (s t : ℚ) :
    binaryB⁻¹ * Adelic.lineUnipotent s t * binaryB =
      Adelic.lineUnipotent (-s-3*t) t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryB, Adelic.lineUnipotent, Adelic.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]
  ring

theorem binaryR_conjugate (s t : ℚ) :
    binaryR⁻¹ * Adelic.lineUnipotent s t * binaryR =
      Adelic.lineUnipotent (-s) t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryR, Adelic.lineUnipotent, Adelic.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

theorem binaryA_normalizes (s t : ℤ) : ∃ s' t' : ℤ,
    binaryA⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * binaryA =
      Adelic.lineUnipotent (s' : ℚ) (t' : ℚ) := by
  refine ⟨s+3*t, -s-2*t, ?_⟩
  simpa only [Int.cast_add, Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat] using
    binaryA_conjugate (s : ℚ) (t : ℚ)

theorem binaryB_normalizes (s t : ℤ) : ∃ s' t' : ℤ,
    binaryB⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * binaryB =
      Adelic.lineUnipotent (s' : ℚ) (t' : ℚ) := by
  refine ⟨-s-3*t, t, ?_⟩
  simpa only [Int.cast_sub, Int.cast_neg, Int.cast_mul, Int.cast_ofNat] using
    binaryB_conjugate (s : ℚ) (t : ℚ)

theorem binaryR_normalizes (s t : ℤ) : ∃ s' t' : ℤ,
    binaryR⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * binaryR =
      Adelic.lineUnipotent (s' : ℚ) (t' : ℚ) := by
  refine ⟨-s, t, ?_⟩
  simpa only [Int.cast_neg] using binaryR_conjugate (s : ℚ) (t : ℚ)

theorem normalizedBadLine_reflection_radical_primitives (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    ∀ reflection ∈ ({binaryB, binaryR} : Set RationalGL3),
      ∃ primitive : HomogeneousPoly n, ∀ s t : ℤ,
        mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c reflection
          (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
        primitive - rationalCoefficientComponent n trivialCharacter
          (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) primitive := by
  intro reflection selected
  rcases selected with rfl | rfl
  · exact mixed_primitive_on_integralRadical_of_coordinate_zero n positive c normalized.1
      ⟨binaryB, binaryB_mem⟩ binaryB_normalizes normalized.2.2.1
  · exact mixed_primitive_on_integralRadical_of_coordinate_zero n positive c normalized.1
      ⟨binaryR, binaryR_mem⟩ binaryR_normalizes normalized.2.2.2

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
