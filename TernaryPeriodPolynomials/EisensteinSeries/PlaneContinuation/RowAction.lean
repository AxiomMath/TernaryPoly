module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.LatticeBounds

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction

noncomputable def rowLinearEquiv (matrix : RealGL3) : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun vector := vector ᵥ* matrix.val
  invFun vector := vector ᵥ* matrix.inv
  map_add' first second := Matrix.add_vecMul _ _ _
  map_smul' scalar vector := Matrix.smul_vecMul _ _ _
  left_inv vector := by
    dsimp only
    rw [Matrix.vecMul_vecMul, matrix.val_inv, Matrix.vecMul_one]
  right_inv vector := by
    dsimp only
    rw [Matrix.vecMul_vecMul, matrix.inv_val, Matrix.vecMul_one]

noncomputable def rowAction (matrix : RealGL3) :
    EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).trans
    ((rowLinearEquiv matrix).trans (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm)).toContinuousLinearEquiv

theorem rowAction_apply (matrix : RealGL3) (vector : EuclideanSpace ℝ (Fin 3)) :
    rowAction matrix vector = WithLp.toLp 2 (vector.ofLp ᵥ* matrix.val) := rfl

theorem summable_transformed_flag_rows
    (equivalence : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    (exponent : ℝ) (exponentBound : exponent < -3) :
    Summable (fun flag : Flags .plane =>
      ‖equivalence (TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.integralFlagLatticeRow flag).val‖ ^ exponent) := by
  let lattice := ZLattice.comap ℝ TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.integralLattice
    equivalence.symm.toLinearMap
  let latticeEquivalence := ZLattice.comap_equiv ℝ TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.integralLattice
    equivalence.symm.toLinearEquiv
  have latticeRank : Module.finrank ℤ lattice = 3 := by
    rw [ZLattice.rank ℝ lattice]
    simp
  have latticeSummable := ZLattice.summable_norm_rpow lattice exponent
    (by simpa only [latticeRank, Nat.cast_ofNat] using exponentBound)
  have rowsInjective := latticeEquivalence.injective.comp
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.integralFlagLatticeRow_injective
  have result : Summable (fun flag : Flags .plane =>
      ‖latticeEquivalence (TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.integralFlagLatticeRow flag)‖ ^ exponent) :=
    latticeSummable.comp_injective rowsInjective
  apply result.congr
  intro flag
  congr 1

theorem summable_flag_row_products (matrix : RealGL3)
    (exponent : ℝ) (exponentBound : exponent < -3) :
    Summable (fun flag : Flags .plane =>
      ‖(WithLp.toLp 2 ((fun column : Fin 3 =>
        (TernaryPeriodPolynomials.PlaneEisensteinContinuation.IntegerReduction.integralFlagRow flag column : ℝ)) ᵥ* matrix.val) :
          EuclideanSpace ℝ (Fin 3))‖ ^ exponent) := by
  have result := summable_transformed_flag_rows (rowAction matrix) exponent exponentBound
  simpa only [rowAction_apply, TernaryPeriodPolynomials.PlaneEisensteinContinuation.LatticeBounds.integralFlagLatticeRow,
    WithLp.ofLp_toLp] using result

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.RowAction
