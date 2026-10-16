module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BinaryCusp

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def integralUpperTranslation : IntegralGL3 :=
  ⟨!![1,0,0;0,1,1;0,0,1], !![1,0,0;0,1,-1;0,0,1], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

def upperTranslation : RationalGL3 :=
  GeneralLinearGroup.map (Int.castRingHom ℚ) integralUpperTranslation

theorem integralUpperTranslation_levi : BadLineLevi integralUpperTranslation := by
  refine ⟨?_,rfl,rfl,rfl,rfl⟩
  rw [arithmeticLevel_mem_iff]
  intro i
  fin_cases i <;> decide

theorem upperTranslation_mem : upperTranslation ∈ rationalLevel :=
  rationalLevel_badLineLevi integralUpperTranslation integralUpperTranslation_levi

theorem upperTranslation_word :
    upperTranslation = binaryA * (binaryA * (binaryB * binaryR)) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTranslation,integralUpperTranslation,GeneralLinearGroup.map_apply,
      binaryA,binaryB,binaryR,Matrix.mul_apply,Fin.sum_univ_three] <;> norm_num

theorem upperTranslation_conjugate (s t : ℚ) :
    upperTranslation⁻¹ * Adelic.lineUnipotent s t * upperTranslation =
      Adelic.lineUnipotent s (s+t) := by
  unfold upperTranslation
  rw [← map_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralUpperTranslation,
      Adelic.lineUnipotent,Adelic.upperUnipotent,Matrix.mul_apply,Fin.sum_univ_three]

theorem upperTranslation_normalizes (s t : ℤ) : ∃ s' t' : ℤ,
    upperTranslation⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * upperTranslation =
      Adelic.lineUnipotent (s' : ℚ) (t' : ℚ) := by
  exact ⟨s,s+t,by simpa using upperTranslation_conjugate (s : ℚ) (t : ℚ)⟩

theorem normalizedBadLine_upper_coordinate (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    mixedBernoulliCoordinate c upperTranslation = mixedBernoulliCoordinate c binaryA +
      binaryASubstitution (mixedBernoulliCoordinate c binaryA) := by
  have br_levi := badLineLevi_mul integralBinaryB integralBinaryR
    integralBinaryB_levi integralBinaryR_levi
  have br_normalizes := radical_normalizes_mul binaryB binaryR
    binaryB_normalizes binaryR_normalizes
  have abr_normalizes := radical_normalizes_mul binaryA (binaryB*binaryR)
    binaryA_normalizes br_normalizes
  have pure_abr : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryA (binaryB*binaryR) = 0 := by
    simpa only [map_mul,integralBinaryA_map,integralBinaryB_map,integralBinaryR_map] using
      pureMixed_levi_bar c normalized.1 integralBinaryA (integralBinaryB*integralBinaryR)
        integralBinaryA_levi br_levi
  have pure_aabr : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryA (binaryA*(binaryB*binaryR)) = 0 := by
    simpa only [map_mul,integralBinaryA_map,integralBinaryB_map,integralBinaryR_map] using
      pureMixed_levi_bar c normalized.1 integralBinaryA
        (integralBinaryA*(integralBinaryB*integralBinaryR)) integralBinaryA_levi
        (badLineLevi_mul _ _ integralBinaryA_levi br_levi)
  have first := mixedBernoulliCoordinate_A_mul n positive c normalized.1
    ⟨binaryB*binaryR,rationalLevel.mul_mem binaryB_mem binaryR_mem⟩ br_normalizes pure_abr
  have second := mixedBernoulliCoordinate_A_mul n positive c normalized.1
    ⟨binaryA*(binaryB*binaryR),rationalLevel.mul_mem binaryA_mem
      (rationalLevel.mul_mem binaryB_mem binaryR_mem)⟩ abr_normalizes pure_aabr
  rw [normalizedBadLine_BR_coordinate_zero n positive f c normalized,map_zero,add_zero] at first
  rw [upperTranslation_word,second,first]

theorem normalizedBadLine_upper_cusp_zero_even (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f) (even : Even n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    upperCuspSubstitution (mixedBernoulliCoordinate c upperTranslation) = 0 := by
  rw [normalizedBadLine_upper_coordinate n positive f c normalized]
  exact normalizedBadLine_upper_polynomial_vanishes n positive f solution even c normalized

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
