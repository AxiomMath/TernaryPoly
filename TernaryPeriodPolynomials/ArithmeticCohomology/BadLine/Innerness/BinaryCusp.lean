module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.MixedBinary

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial Matrix

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem mixedBernoulliCoordinate_zero_of_primitive (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (levi : RationalGL3) (primitive : HomogeneousPoly n)
    (values : ∀ s t : ℤ,
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
      primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) primitive) :
    mixedBernoulliCoordinate c levi = 0 := by
  have first := values 1 0
  have second := values 0 1
  simp only [Int.cast_one,Int.cast_zero] at first second
  rw [mixedBernoulliCoordinate_eq_pair, first, second]
  exact radical_coboundary_bernoulli_zero n positive primitive

theorem mixed_product_primitive (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (first second : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      first.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * first.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ))
    (pure_product : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c first.val second.val = 0)
    (a b : HomogeneousPoly n)
    (first_values : ∀ s t : ℤ,
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c first.val
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) = a - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) a)
    (second_values : ∀ s t : ℤ,
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c second.val
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) = b - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) b) (s t : ℤ) :
    mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c
      (first.val*second.val) (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
    (a + rationalCoefficientComponent n trivialCharacter first.val b) -
      rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent (s : ℚ) (t : ℚ))
        (a + rationalCoefficientComponent n trivialCharacter first.val b) := by
  obtain ⟨s',t',conjugate⟩ := normalizes s t
  have relation := mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c first
    ⟨Adelic.lineUnipotent (s : ℚ) (t : ℚ),rationalLevel_lineUnipotent s t⟩
    second.val pure_product
  rw [first_values, conjugate, second_values, ← conjugate,
    representation_coboundary_conjugate] at relation
  rw [relation, map_add]
  abel

theorem normalizedBadLine_BR_coordinate_zero (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) : mixedBernoulliCoordinate c (binaryB*binaryR) = 0 := by
  obtain ⟨a,ha⟩ := normalizedBadLine_reflection_radical_primitives n positive f c normalized
    binaryB (by simp)
  obtain ⟨b,hb⟩ := normalizedBadLine_reflection_radical_primitives n positive f c normalized
    binaryR (by simp)
  have pure_product : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryB binaryR = 0 := by
    simpa only [integralBinaryB_map,integralBinaryR_map] using
      pureMixed_levi_bar c normalized.1 integralBinaryB integralBinaryR
        integralBinaryB_levi integralBinaryR_levi
  exact mixedBernoulliCoordinate_zero_of_primitive n positive c (binaryB*binaryR)
    (a + rationalCoefficientComponent n trivialCharacter binaryB b)
    (mixed_product_primitive n c ⟨binaryB,binaryB_mem⟩ ⟨binaryR,binaryR_mem⟩
      binaryB_normalizes pure_product a b ha hb)

theorem mixedBernoulliCoordinate_one (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) : mixedBernoulliCoordinate c 1 = 0 := by
  have radical_one : Adelic.lineUnipotent (0 : ℚ) 0 = 1 := (Adelic.lineUnipotentHom ℚ).map_one
  have edge_zero (s t : ℤ) : mixedValue rationalLevel
      (rationalCoefficientComponent n trivialCharacter) c 1
      (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) = 0 := by
    have first := pureMixed_radical_bar c pure 0 0 s t
    have second := pureMixed_radical_bar c pure s t 0 0
    simp only [Int.cast_zero,radical_one] at first second
    simp only [mixedValue,inv_one,one_mul,mul_one,first,second,sub_self]
  rw [mixedBernoulliCoordinate_eq_pair]
  have first := edge_zero 1 0
  have second := edge_zero 0 1
  simp only [Int.cast_zero,Int.cast_one] at first second
  rw [first,second]
  simp only [radicalPairCoordinate, Submodule.coe_zero,
    bernoulliOperator_eq_of_pderiv_zero n (X 1) 0 (by simp),
    bernoulliOperator_eq_of_pderiv_zero n (X 2) 0 (by simp),mul_zero,sub_self]

theorem binaryA_cube : binaryA * (binaryA * binaryA) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryA, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

theorem mixedBernoulliCoordinate_A_norm (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) :
    mixedBernoulliCoordinate c binaryA + binaryASubstitution (mixedBernoulliCoordinate c binaryA) +
      binaryASubstitution (binaryASubstitution (mixedBernoulliCoordinate c binaryA)) = 0 := by
  have pure_square : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryA binaryA = 0 := by
    simpa only [integralBinaryA_map] using pureMixed_levi_bar c pure integralBinaryA integralBinaryA
      integralBinaryA_levi integralBinaryA_levi
  have pure_cube : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryA (binaryA*binaryA) = 0 := by
    simpa only [map_mul,integralBinaryA_map] using
      pureMixed_levi_bar c pure integralBinaryA (integralBinaryA*integralBinaryA)
        integralBinaryA_levi (badLineLevi_mul _ _ integralBinaryA_levi integralBinaryA_levi)
  have square := mixedBernoulliCoordinate_A_mul n positive c pure ⟨binaryA,binaryA_mem⟩
    binaryA_normalizes pure_square
  have cube := mixedBernoulliCoordinate_A_mul n positive c pure
    ⟨binaryA*binaryA,rationalLevel.mul_mem binaryA_mem binaryA_mem⟩
    (radical_normalizes_mul binaryA binaryA binaryA_normalizes binaryA_normalizes) pure_cube
  rw [binaryA_cube, mixedBernoulliCoordinate_one n c pure, square, map_add] at cube
  simpa only [add_assoc] using cube.symm

def upperCuspSubstitution : Poly →ₐ[ℂ] Poly := bind₁ ![X 0,X 1,0]

theorem upperCusp_binaryA_twice (p : Poly) :
    upperCuspSubstitution (binaryASubstitution (binaryASubstitution p)) = cuspSubstitution p := by
  have hom_eq : upperCuspSubstitution.comp (binaryASubstitution.comp binaryASubstitution) =
      cuspSubstitution := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [upperCuspSubstitution,binaryASubstitution,cuspSubstitution,map_ofNat] <;> ring
  exact congrArg (fun hom : Poly →ₐ[ℂ] Poly => hom p) hom_eq

theorem normalizedBadLine_upper_polynomial_vanishes (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f) (even : Even n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    upperCuspSubstitution (mixedBernoulliCoordinate c binaryA +
      binaryASubstitution (mixedBernoulliCoordinate c binaryA)) = 0 := by
  have norm := congrArg upperCuspSubstitution (mixedBernoulliCoordinate_A_norm n positive c normalized.1)
  rw [map_add,upperCusp_binaryA_twice,normalizedBadLine_cusp_zero positive f solution even c normalized,
    add_zero,map_zero] at norm
  exact norm

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
