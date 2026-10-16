module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Cohomological.LowestWeight

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

set_option backward.isDefEq.respectTransparency false

theorem cohomological_lowering_nonzero_above {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℝ)
    (above : (degree : ℝ) + 3 < weight) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    cuspLoweringOperator cusp vector ≠ 0 := by
  intro zero
  have value := cuspCasimir_eq_of_lowering_zero cusp weight (((degree : ℝ) + 1) * ((degree : ℝ) + 3))
    vector nonzero rotation (cohomological_casimir_eigenvector cohomological vector) zero
  have product : 0 < (weight - degree - 3) * (weight + degree + 1) := by
    apply mul_pos
    · linarith
    · linarith [Nat.cast_nonneg (α := ℝ) degree]
  nlinarith

theorem cohomological_positive_weight_spectrum {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ) (positive : 0 < weight)
    (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    ∃ step : ℕ, weight = (degree : ℤ) + 3 + 2 * step := by
  have all : ∀ size : ℕ, ∀ integerWeight : ℤ, integerWeight.natAbs = size → 0 < integerWeight →
      ∀ smoothVector : cusp.smooth, smoothVector ≠ 0 →
        cuspRotationOperator cusp smoothVector = (Complex.I * (integerWeight : ℂ)) • smoothVector →
        ∃ step : ℕ, integerWeight = (degree : ℤ) + 3 + 2 * step := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size induction =>
      intro integerWeight size_eq weight_positive smoothVector vector_nonzero vector_rotation
      have positive_real : (0 : ℝ) < integerWeight := by exact_mod_cast weight_positive
      have rotation_real : cuspRotationOperator cusp smoothVector =
          (Complex.I * ((integerWeight : ℝ) : ℂ)) • smoothVector := by
        simpa only [Complex.ofReal_intCast] using vector_rotation
      have gap := cohomological_rotation_weight_gap cohomological integerWeight smoothVector vector_nonzero rotation_real
      rw [abs_of_pos positive_real] at gap
      have lower : (degree : ℤ) + 3 ≤ integerWeight := by exact_mod_cast gap
      by_cases bottom : integerWeight = (degree : ℤ) + 3
      · exact ⟨0, by simpa using bottom⟩
      · have above : (degree : ℤ) + 3 < integerWeight := lt_of_le_of_ne lower (Ne.symm bottom)
        have above_real : (degree : ℝ) + 3 < integerWeight := by exact_mod_cast above
        have lowered_nonzero := cohomological_lowering_nonzero_above cohomological integerWeight above_real
          smoothVector vector_nonzero rotation_real
        have lowered_rotation : cuspRotationOperator cusp (cuspLoweringOperator cusp smoothVector) =
            (Complex.I * ((integerWeight - 2 : ℤ) : ℂ)) • cuspLoweringOperator cusp smoothVector := by
          simpa only [Int.cast_sub, Int.cast_ofNat] using
            cuspLowering_weight cusp integerWeight smoothVector vector_rotation
        have smaller : (integerWeight - 2).natAbs < size := by
          rw [← size_eq, Int.natAbs_lt_iff_sq_lt]
          have large : (3 : ℤ) < integerWeight := by omega
          nlinarith
        have lowered_positive : 0 < integerWeight - 2 := by omega
        obtain ⟨step, value⟩ := induction (integerWeight - 2).natAbs smaller (integerWeight - 2) rfl
          lowered_positive (cuspLoweringOperator cusp smoothVector) lowered_nonzero lowered_rotation
        refine ⟨step + 1, ?_⟩
        push_cast
        omega
  exact all weight.natAbs weight rfl positive vector nonzero rotation

theorem cohomological_negative_weight_spectrum {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ) (negative : weight < 0)
    (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    ∃ step : ℕ, weight = -((degree : ℤ) + 3 + 2 * step) := by
  have reflected : cuspRotationOperator cusp (cuspSmoothAction cusp (atInfinity binaryReflection) vector) =
      (Complex.I * ((-weight : ℤ) : ℂ)) • cuspSmoothAction cusp (atInfinity binaryReflection) vector := by
    rw [cuspRotation_reflection, rotation, map_smul, ← neg_smul, Int.cast_neg, mul_neg]
  obtain ⟨step, value⟩ := cohomological_positive_weight_spectrum cohomological (-weight) (by omega)
    (cuspSmoothAction cusp (atInfinity binaryReflection) vector)
    (cuspSmoothAction_ne_zero cusp _ vector nonzero) reflected
  exact ⟨step, by omega⟩

theorem cohomological_integer_weight_spectrum {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ)
    (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (rotation : cuspRotationOperator cusp vector = (Complex.I * (weight : ℂ)) • vector) :
    ∃ step : ℕ, weight.natAbs = degree + 3 + 2 * step := by
  rcases lt_trichotomy weight 0 with negative | zero | positive
  · obtain ⟨step, value⟩ := cohomological_negative_weight_spectrum cohomological weight negative vector nonzero rotation
    refine ⟨step, ?_⟩
    rw [value, Int.natAbs_neg]
    exact_mod_cast (show (degree : ℤ) + 3 + 2 * step = ↑(degree + 3 + 2 * step) by push_cast; rfl)
  · have rotation_real : cuspRotationOperator cusp vector = (Complex.I * ((weight : ℝ) : ℂ)) • vector := by
      simpa only [Complex.ofReal_intCast] using rotation
    have gap := cohomological_rotation_weight_gap cohomological weight vector nonzero rotation_real
    simp only [zero, Int.cast_zero, abs_zero] at gap
    have : (0 : ℝ) < degree + 3 := by positivity
    linarith
  · obtain ⟨step, value⟩ := cohomological_positive_weight_spectrum cohomological weight positive vector nonzero rotation
    refine ⟨step, ?_⟩
    have cast : (↑weight.natAbs : ℤ) = (degree : ℤ) + 3 + 2 * step := by
      rw [Int.natAbs_of_nonneg positive.le, value]
    exact_mod_cast cast

theorem cohomological_hilbert_projection_spectrum {cusp : CuspidalRepresentation} {degree : ℕ}
    (cohomological : Cohomological cusp degree) (weight : ℤ)
    (forbidden : ¬ ∃ step : ℕ, weight.natAbs = degree + 3 + 2 * step) (vector : cusp.H) :
    cuspRotationProjection cusp weight vector = 0 := by
  have closed : IsClosed {vector : cusp.H | cuspRotationProjection cusp weight vector = 0} :=
    isClosed_eq (cuspRotationProjection cusp weight).continuous continuous_const
  have smooth_zero : (cusp.smooth : Set cusp.H) ⊆ {vector | cuspRotationProjection cusp weight vector = 0} := by
    intro vector member
    have zero : cuspSmoothRotationProjection cusp weight ⟨vector, member⟩ = 0 := by
      by_contra nonzero
      exact forbidden (cohomological_integer_weight_spectrum cohomological weight _ nonzero
        (cuspSmoothRotationProjection_eigenvector cusp weight ⟨vector, member⟩))
    exact congrArg Subtype.val zero
  exact closure_minimal smooth_zero closed ((cohomological_smooth_dense cohomological) vector)

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
