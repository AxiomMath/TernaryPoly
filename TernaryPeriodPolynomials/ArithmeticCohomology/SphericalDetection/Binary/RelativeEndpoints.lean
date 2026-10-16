module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.RelativeNormalForm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

noncomputable section

namespace TernaryPeriodPolynomials.SphericalDetection.Helpers

theorem binaryRelativeRaising_supported_zero (cusp : CuspidalRepresentation) (degree : ℕ) (weight : ℤ)
    (vector : binarySmoothValues cusp (Fin (degree + 2)))
    (support : ∀ position : Fin (degree + 1), vector position.succ = 0)
    (position : Fin (degree + 2)) (nonzero : position ≠ 0) :
    binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) weight vector position = 0 := by
  have value_zero (position : Fin (degree + 2)) (nonzero : position ≠ 0) : vector position = 0 := by
    obtain ⟨position, rfl⟩ := Fin.exists_succ_eq.mpr nonzero
    exact support position
  revert nonzero
  refine Fin.lastCases ?_ (fun position => ?_) position
  · intro _
    rw [binaryRelativeRaising_last, value_zero _ (by simp), map_zero]
  · intro nonzero
    rw [binaryRelativeRaising_castSucc, support, value_zero _ nonzero, smul_zero, map_zero, add_zero]

theorem binaryRelative_normal_form_equations (cusp : CuspidalRepresentation) (degree : ℕ)
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0) :
    cuspRaisingOperator cusp (-2 - (degree + 1 : ℕ)) (lower 0) =
      cuspLoweringOperator cusp (2 - (degree + 1 : ℕ)) (upper 0) ∧
    ∀ position : Fin (degree + 1),
      (Complex.I * ((degree + 1 - position.val : ℕ) : ℂ)) • upper position.castSucc +
        cuspLoweringOperator cusp (binaryUnitaryWeight degree 2 position.succ) (upper position.succ) = 0 := by
  constructor
  · have identity := congrFun closed 0
    have first_formula := binaryRelativeRaising_castSucc cusp degree (-2) lower (0 : Fin (degree + 1))
    simp only [Fin.castSucc_zero] at first_formula
    rw [first_formula, support, smul_zero, zero_add, binaryRelativeLowering_zero] at identity
    simpa only [binaryUnitaryWeight, Fin.val_castSucc, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero] using identity
  · intro position
    have identity := congrFun closed position.succ
    rw [binaryRelativeRaising_supported_zero cusp degree (-2) lower support _ (Fin.succ_ne_zero _),
      binaryRelativeLowering_succ] at identity
    exact identity.symm

theorem binaryRelative_normal_form_upper_zero (cusp : CuspidalRepresentation) (degree : ℕ)
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0)
    (endpoint_zero : upper (Fin.last (degree + 1)) = 0) : upper = 0 := by
  have equations := (binaryRelative_normal_form_equations cusp degree lower upper closed support).2
  funext position
  change upper position = 0
  refine Fin.reverseInduction endpoint_zero (fun position successor_zero => ?_) position
  have identity := equations position
  rw [successor_zero, map_zero, add_zero] at identity
  apply (smul_eq_zero.mp identity).resolve_left
  apply mul_ne_zero Complex.I_ne_zero
  have positive : 0 < degree + 1 - position.val := by omega
  exact_mod_cast (ne_of_gt positive)

theorem binaryRelative_normal_form_endpoint_nonzero (cusp : CuspidalRepresentation) (degree : ℕ)
    (lower upper : binarySmoothValues cusp (Fin (degree + 2)))
    (closed : binaryRelativeRaising cusp (binaryWeightBasis (degree + 1)) (-2) lower =
      binaryRelativeLowering cusp (binaryWeightBasis (degree + 1)) 2 upper)
    (support : ∀ position : Fin (degree + 1), lower position.succ = 0)
    (nonzero : lower ≠ 0 ∨ upper ≠ 0) :
    lower 0 ≠ 0 ∨ upper (Fin.last (degree + 1)) ≠ 0 := by
  by_contra endpoints_zero
  push Not at endpoints_zero
  have lower_zero : lower = 0 := by
    funext position
    exact Fin.cases endpoints_zero.1 support position
  have upper_zero := binaryRelative_normal_form_upper_zero cusp degree lower upper closed support endpoints_zero.2
  exact nonzero.elim (fun not_zero => not_zero lower_zero) (fun not_zero => not_zero upper_zero)

theorem cohomological_exists_endpoint_ladder_system (cusp : CuspidalRepresentation)
    (spherical : SphericalCusp cusp) {degree : ℕ} (cohomological : Cohomological cusp degree) :
    ∃ (level : Subgroup BinaryFiniteGL) (lower : cuspAffineSmoothValues cusp)
      (upper : binarySmoothValues cusp (Fin (degree + 2))),
      IsOpen (level : Set BinaryFiniteGL) ∧ IsCompact (level : Set BinaryFiniteGL) ∧
      lower ∈ cuspFiniteWeightValues cusp level (-2 - (degree + 1 : ℕ)) ∧
      (∀ position, upper position ∈ cuspFiniteWeightValues cusp level (binaryUnitaryWeight degree 2 position)) ∧
      (lower ≠ 0 ∨ upper (Fin.last (degree + 1)) ≠ 0) ∧
      cuspRaisingOperator cusp (-2 - (degree + 1 : ℕ)) lower =
        cuspLoweringOperator cusp (2 - (degree + 1 : ℕ)) (upper 0) ∧
      ∀ position : Fin (degree + 1),
        (Complex.I * ((degree + 1 - position.val : ℕ) : ℂ)) • upper position.castSucc +
          cuspLoweringOperator cusp (binaryUnitaryWeight degree 2 position.succ) (upper position.succ) = 0 := by
  obtain ⟨level, _, lower, upper, level_open, level_compact, _, _, _, _, lower_mem, upper_mem,
    _, _, closed, support, nonzero⟩ := cohomological_exists_relative_normal_form cusp spherical cohomological
  refine ⟨level, lower 0, upper, level_open, level_compact, ?_, upper_mem,
    binaryRelative_normal_form_endpoint_nonzero cusp degree lower upper closed support nonzero,
    binaryRelative_normal_form_equations cusp degree lower upper closed support⟩
  simpa only [binaryUnitaryWeight, Fin.val_zero, Nat.cast_zero, mul_zero, add_zero] using lower_mem 0

end TernaryPeriodPolynomials.SphericalDetection.Helpers
