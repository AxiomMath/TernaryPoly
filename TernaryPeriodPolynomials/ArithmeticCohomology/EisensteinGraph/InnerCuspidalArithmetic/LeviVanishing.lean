module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerRadical
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.CentralVanishing

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def lineScalarReflection (R : Type) [CommRing R] : GeneralLinearGroup (Fin 3) R :=
  lineLevi (-1) 1

theorem map_lineScalarReflection {R S : Type} [CommRing R] [CommRing S]
    (homomorphism : R →+* S) :
    GeneralLinearGroup.map homomorphism (lineScalarReflection R) = lineScalarReflection S := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [GeneralLinearGroup.map_apply, lineScalarReflection, lineLevi_val]

theorem lineScalarReflection_inverse (R : Type) [CommRing R] :
    (lineScalarReflection R)⁻¹ = lineScalarReflection R := by
  change ((lineLeviHom R) (-1, 1))⁻¹ = (lineLeviHom R) (-1, 1)
  rw [← map_inv]
  simp

theorem action_lineScalarReflection_binary (polynomial : Binary.Poly) :
    action (-1) (lineScalarReflection ℂ) (binaryPolynomialEmbedding polynomial) =
      -binaryPolynomialEmbedding polynomial := by
  rw [action_apply, lineScalarReflection_inverse]
  have determinant : determinantCharacter (-1) (lineScalarReflection ℂ) = -1 := by
    simp [determinantCharacter, GeneralLinearGroup.val_det_apply,
      lineScalarReflection, lineLevi_val, Matrix.det_fin_three]
  rw [determinant, neg_one_smul]
  apply congrArg Neg.neg
  change bind₁ _ ((MvPolynomial.rename (Fin.succ : Fin 2 → Fin 3)) polynomial) = _
  rw [bind₁_rename]
  have forms : linearForm (lineScalarReflection ℂ).val ∘ (Fin.succ : Fin 2 → Fin 3) =
      fun index => (X index.succ : Poly) := by
    funext index
    fin_cases index <;>
      simp [linearForm, lineScalarReflection, lineLevi_val, Fin.sum_univ_three]
  rw [forms]
  have substitution : bind₁ (fun index : Fin 2 => (X index.succ : Poly)) =
      binaryPolynomialEmbedding := by
    ext index
    simp [binaryPolynomialEmbedding]
  rw [substitution]

theorem rationalCoefficientComponent_lineScalarReflection_binary (degree : ℕ)
    (polynomial : Binary.HomogeneousPoly degree) :
    rationalCoefficientComponent degree trivialCharacter (lineScalarReflection ℚ)
      (binaryHomogeneousEmbedding degree polynomial) =
        -binaryHomogeneousEmbedding degree polynomial := by
  apply Subtype.ext
  change ((1 : ℂ) • homogeneousAction degree (-1)
    (GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (GeneralLinearGroup.map (algebraMap ℚ ℝ) (lineScalarReflection ℚ)))
        (binaryHomogeneousEmbedding degree polynomial)).val = _
  rw [one_smul, map_lineScalarReflection, map_lineScalarReflection]
  exact action_lineScalarReflection_binary polynomial.val

theorem radicalShear_integer_invariant_derivative (index : Fin 2) (polynomial : Poly)
    (invariant : ∀ parameter : ℤ,
      bind₁ (fun coordinate : Fin 3 =>
        if coordinate = 0 then X 0 - C (parameter : ℂ) * X index.succ else X coordinate)
          polynomial = polynomial) : pderiv 0 polynomial = 0 := by
  have injective : Function.Injective (fun parameter : ℤ => (C (parameter : ℂ) : Poly)) :=
    (MvPolynomial.C_injective (Fin 3) ℂ).comp Int.cast_injective
  have familyEquality : radicalShearFamily index polynomial = Polynomial.C polynomial := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective injective).mono
    rintro parameter ⟨integer, rfl⟩
    change Polynomial.eval (C (integer : ℂ)) (radicalShearFamily index polynomial) =
      Polynomial.eval (C (integer : ℂ)) (Polynomial.C polynomial)
    rw [radicalShearFamily_eval, Polynomial.eval_C]
    exact invariant integer
  have coefficient := congrArg (fun family : Polynomial Poly => family.coeff 1) familyEquality
  rw [radicalShearFamily_coeff_one, Polynomial.coeff_C] at coefficient
  simp only [one_ne_zero, ↓reduceIte] at coefficient
  exact (mul_eq_zero.mp coefficient).resolve_left
    (neg_ne_zero.mpr (MvPolynomial.X_ne_zero index.succ))

theorem standardBadLineInvariant_binary (degree : ℕ)
    (polynomial : semidirectRadicalInvariants integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)) :
    ∃ binary : Binary.HomogeneousPoly degree,
      binaryHomogeneousEmbedding degree binary = polynomial.val := by
  apply (show polynomial.val ∈ (binaryHomogeneousEmbedding degree).range from ?_)
  rw [binaryHomogeneousEmbedding_range_eq_derivativeKernel]
  change pderiv 0 polynomial.val.val = 0
  apply radicalShear_integer_invariant_derivative 0 polynomial.val.val
  intro parameter
  have invariant : radicalRepresentation degree (Multiplicative.ofAdd (parameter, 0))
      polynomial.val = polynomial.val := by
    rw [← standardBadLineRepresentation_radical]
    exact polynomial.property (Multiplicative.ofAdd (parameter, 0))
  change rationalCoefficientComponent degree trivialCharacter
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (lineUnipotent parameter 0))
      polynomial.val = polynomial.val at invariant
  rw [map_lineUnipotent] at invariant
  have evaluated := congrArg (fun value : HomogeneousPoly degree => value.val) invariant
  rw [rationalCoefficientComponent_lineUnipotent] at evaluated
  have forms : (fun coordinate : Fin 3 =>
      if coordinate = 0 then X 0 - C (parameter : ℂ) * X (0 : Fin 2).succ else X coordinate) =
    (![X 0 - C (parameter : ℂ) * X 1, X 1, X 2] : Fin 3 → Poly) := by
    funext coordinate
    fin_cases coordinate <;> simp
  rw [forms]
  simpa using evaluated

def badLineLeviReflection : ℤˣ × binaryArithmeticLevel := (-1, 1)

theorem badLineLeviReflection_central (element : ℤˣ × binaryArithmeticLevel) :
    badLineLeviReflection * element = element * badLineLeviReflection := by
  apply Prod.ext
  · exact mul_comm _ _
  · exact (one_mul _).trans (mul_one _).symm

theorem standardBadLineSemidirectEquiv_inr (element : ℤˣ × binaryArithmeticLevel) :
    standardBadLineSemidirectEquiv (SemidirectProduct.inr element) =
      integralBadLineStabilizerEquiv (integralBadLineLeviSection element) := by
  change integralBadLineStabilizerEquiv
    (integralBadLineRadicalEmbedding 1 * integralBadLineLeviSection element) = _
  rw [map_one, one_mul]

theorem standardBadLineSemidirectEquiv_reflection :
    (standardBadLineSemidirectEquiv (SemidirectProduct.inr badLineLeviReflection)).val =
      lineScalarReflection ℚ := by
  rw [standardBadLineSemidirectEquiv_inr]
  change GeneralLinearGroup.map (Int.castRingHom ℚ) (lineScalarReflection ℤ) = _
  exact map_lineScalarReflection _

theorem standardBadLineInvariant_reflection (degree : ℕ)
    (polynomial : semidirectRadicalInvariants integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)) :
    semidirectInvariantRepresentation integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree) badLineLeviReflection polynomial = -polynomial := by
  apply Subtype.ext
  change rationalCoefficientComponent degree trivialCharacter
    (standardBadLineSemidirectEquiv (SemidirectProduct.inr badLineLeviReflection)).val
      polynomial.val = -polynomial.val
  rw [standardBadLineSemidirectEquiv_reflection]
  obtain ⟨binary, equality⟩ := standardBadLineInvariant_binary degree polynomial
  rw [← equality]
  exact rationalCoefficientComponent_lineScalarReflection_binary degree binary

theorem standardBadLineLeviH2_zero (degree : ℕ)
    (coordinate : InhomogeneousH2
      (semidirectInvariantRepresentation integralBadLineSplitting.conjAct
        (standardBadLineRepresentation degree))) : coordinate = 0 :=
  inhomogeneousH2_zero_of_central_neg _ badLineLeviReflection badLineLeviReflection_central
    (standardBadLineInvariant_reflection degree) coordinate

theorem standardBadLineMixedMap_injective (degree : ℕ) :
    Function.Injective (radicalKernelMixedMap integralBadLineSplitting.conjAct
      (standardBadLineRepresentation degree)) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro coordinate zero
    obtain ⟨leviCoordinate, equality⟩ := radicalKernelMixedMap_zero_mem_inflation
      integralBadLineSplitting.conjAct (standardBadLineRepresentation degree) coordinate zero
    rw [standardBadLineLeviH2_zero degree leviCoordinate, map_zero] at equality
    exact Subtype.ext equality.symm
  · exact bot_le

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
