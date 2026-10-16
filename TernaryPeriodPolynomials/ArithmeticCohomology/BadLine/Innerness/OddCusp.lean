module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.BinaryCovariance

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem mixedBernoulliCoordinate_R_mul (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (levi : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      levi.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * levi.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ))
    (pure_product : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryR levi.val = 0) :
    mixedBernoulliCoordinate c (binaryR * levi.val) = mixedBernoulliCoordinate c binaryR +
      binaryRSubstitution (mixedBernoulliCoordinate c levi.val) := by
  let values := fun x : ℤ × ℤ => mixedValue rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c levi.val
      (integralRadicalHom (Multiplicative.ofAdd x))
  have covariance := radicalPairCoordinate_binaryR n positive values
    (mixedValue_integralRadical_cocycle n c pure levi normalizes)
  have first := mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c ⟨binaryR,binaryR_mem⟩
    ⟨Adelic.lineUnipotent 1 0, by simpa using rationalLevel_lineUnipotent 1 0⟩
    levi.val pure_product
  have second := mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c ⟨binaryR,binaryR_mem⟩
    ⟨Adelic.lineUnipotent 0 1, by simpa using rationalLevel_lineUnipotent 0 1⟩
    levi.val pure_product
  simp only [binaryR_conjugate,neg_zero] at first second
  simp only [mixedBernoulliCoordinate_eq_pair]
  rw [first,second,radicalPairCoordinate_add]
  congr 1

theorem mixedBernoulliCoordinate_T_mul (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (levi : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      levi.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * levi.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ))
    (pure_product : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c upperTranslation levi.val = 0) :
    mixedBernoulliCoordinate c (upperTranslation * levi.val) =
      mixedBernoulliCoordinate c upperTranslation +
      upperTranslationSubstitution (mixedBernoulliCoordinate c levi.val) := by
  let values := fun x : ℤ × ℤ => mixedValue rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c levi.val
      (integralRadicalHom (Multiplicative.ofAdd x))
  have covariance := radicalPairCoordinate_upperTranslation n positive values
    (mixedValue_integralRadical_cocycle n c pure levi normalizes)
  have first := mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c ⟨upperTranslation,upperTranslation_mem⟩
    ⟨Adelic.lineUnipotent 1 0, by simpa using rationalLevel_lineUnipotent 1 0⟩
    levi.val pure_product
  have second := mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c ⟨upperTranslation,upperTranslation_mem⟩
    ⟨Adelic.lineUnipotent 0 1, by simpa using rationalLevel_lineUnipotent 0 1⟩
    levi.val pure_product
  simp only [upperTranslation_conjugate,add_zero,zero_add] at first second
  simp only [mixedBernoulliCoordinate_eq_pair]
  rw [first,second,radicalPairCoordinate_add]
  congr 1

theorem upperTranslation_reflection :
    upperTranslation * (binaryR * upperTranslation) = binaryR := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTranslation,integralUpperTranslation,binaryR,
      Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three]

theorem upperCusp_translation (p : Poly) :
    upperCuspSubstitution (upperTranslationSubstitution p) = upperCuspSubstitution p := by
  have hom_eq : upperCuspSubstitution.comp upperTranslationSubstitution = upperCuspSubstitution := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [upperCuspSubstitution,upperTranslationSubstitution]
  exact congrArg (fun h : Poly →ₐ[ℂ] Poly => h p) hom_eq

theorem radicalPairCoordinate_homogeneous (n : ℕ) (positive : 0 < n)
    (a b : HomogeneousPoly n) : (radicalPairCoordinate n a b).IsHomogeneous (n+1) := by
  unfold radicalPairCoordinate
  rw [← bernoulliEnd_apply n positive (X 1) (isHomogeneous_X ℂ 1) (by simp),
    ← bernoulliEnd_apply n positive (X 2) (isHomogeneous_X ℂ 2) (by simp)]
  simpa only [Nat.add_comm] using
      ((isHomogeneous_X ℂ (2 : Fin 3)).mul (bernoulliEnd n positive (X 1)
        (isHomogeneous_X ℂ 1) a).property).sub
        ((isHomogeneous_X ℂ (1 : Fin 3)).mul (bernoulliEnd n positive (X 2)
          (isHomogeneous_X ℂ 2) b).property)

theorem upperCusp_reflection_even (m : ℕ) (even : Even m)
    (p : HomogeneousPoly m) (independent : pderiv 0 p.val = 0) :
    upperCuspSubstitution (binaryRSubstitution p.val) = upperCuspSubstitution p.val := by
  have projection := removeFirstVariable_eq_of_pderiv_zero p.val independent
  have lhs_eq : upperCuspSubstitution (binaryRSubstitution p.val) = bind₁ ![0,-X 1,0] p.val := by
    conv_lhs => rw [← projection]
    have hom_eq : upperCuspSubstitution.comp (binaryRSubstitution.comp removeFirstVariable) =
        bind₁ ![0,-X 1,0] := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [upperCuspSubstitution,binaryRSubstitution,removeFirstVariable]
    exact congrArg (fun h : Poly →ₐ[ℂ] Poly => h p.val) hom_eq
  have rhs_eq : upperCuspSubstitution p.val = bind₁ ![0,X 1,0] p.val := by
    conv_lhs => rw [← projection]
    have hom_eq : upperCuspSubstitution.comp removeFirstVariable = bind₁ ![0,X 1,0] := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [upperCuspSubstitution,removeFirstVariable]
    exact congrArg (fun h : Poly →ₐ[ℂ] Poly => h p.val) hom_eq
  rw [lhs_eq,rhs_eq]
  have scaled := homogeneous_aeval_scale p (![0,X 1,0] : Fin 3 → Poly) (-1)
  have vector_eq : (fun i => (-1 : Poly) * (![0,X 1,0] : Fin 3 → Poly) i) = ![0,-X 1,0] := by
    funext i
    fin_cases i <;> simp
  simpa only [vector_eq,even.neg_one_pow,one_mul,aeval_eq_bind₁] using scaled

theorem normalizedBadLine_upper_cusp_zero_odd (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (odd : Odd n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    upperCuspSubstitution (mixedBernoulliCoordinate c upperTranslation) = 0 := by
  have pure_rt : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c binaryR upperTranslation = 0 := by
    simpa only [integralBinaryR_map,upperTranslation] using pureMixed_levi_bar c normalized.1
      integralBinaryR integralUpperTranslation integralBinaryR_levi integralUpperTranslation_levi
  have pure_trt : barValue rationalLevel (rationalCoefficientComponent n trivialCharacter)
      c upperTranslation (binaryR*upperTranslation) = 0 := by
    simpa only [map_mul,integralBinaryR_map,upperTranslation] using pureMixed_levi_bar c normalized.1
      integralUpperTranslation (integralBinaryR*integralUpperTranslation) integralUpperTranslation_levi
        (badLineLevi_mul _ _ integralBinaryR_levi integralUpperTranslation_levi)
  have rt := mixedBernoulliCoordinate_R_mul n positive c normalized.1
    ⟨upperTranslation,upperTranslation_mem⟩ upperTranslation_normalizes pure_rt
  have trt := mixedBernoulliCoordinate_T_mul n positive c normalized.1
    ⟨binaryR*upperTranslation,rationalLevel.mul_mem binaryR_mem upperTranslation_mem⟩
    (radical_normalizes_mul binaryR upperTranslation binaryR_normalizes upperTranslation_normalizes)
    pure_trt
  rw [upperTranslation_reflection,rt,normalized.2.2.2,zero_add] at trt
  have cusp := congrArg upperCuspSubstitution trt
  rw [map_zero,map_add,upperCusp_translation] at cusp
  have homogeneous : (mixedBernoulliCoordinate c upperTranslation).IsHomogeneous (n+1) := by
    rw [mixedBernoulliCoordinate_eq_pair]
    exact radicalPairCoordinate_homogeneous n positive _ _
  have independent := mixedBernoulliCoordinate_pderiv_zero n positive c normalized.1
    ⟨upperTranslation,upperTranslation_mem⟩ upperTranslation_normalizes
  have even : Even (n+1) := by
    rcases odd with ⟨k,hk⟩
    exact ⟨k+1,by omega⟩
  rw [upperCusp_reflection_even (n+1) even ⟨_,homogeneous⟩ independent] at cusp
  have doubled : (2 : ℂ) • upperCuspSubstitution (mixedBernoulliCoordinate c upperTranslation) = 0 := by
    simpa only [two_smul] using cusp.symm
  exact (smul_eq_zero.mp doubled).resolve_left (by norm_num)

theorem normalizedBadLine_upper_cusp_zero (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    upperCuspSubstitution (mixedBernoulliCoordinate c upperTranslation) = 0 := by
  rcases Nat.even_or_odd n with even | odd
  · exact normalizedBadLine_upper_cusp_zero_even n positive f solution even c normalized
  · exact normalizedBadLine_upper_cusp_zero_odd n positive f odd c normalized

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
