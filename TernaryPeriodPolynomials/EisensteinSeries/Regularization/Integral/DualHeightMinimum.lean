module

public import TernaryPeriodPolynomials.EisensteinSeries.Regularization.Real.HeightOrthogonal

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinRegularization.Helpers

def generalLinearInverseTranspose (R : Type*) [CommRing R] : GL3 R →* GL3 R where
  toFun matrix := ⟨matrix.inv.transpose, matrix.val.transpose, by
    rw [← Matrix.transpose_mul, matrix.val_inv, Matrix.transpose_one], by
    rw [← Matrix.transpose_mul, matrix.inv_val, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    exact Matrix.transpose_one
  map_mul' first second := by
    apply Units.ext
    change (second.inv * first.inv).transpose = first.inv.transpose * second.inv.transpose
    exact Matrix.transpose_mul _ _

theorem generalLinearInverseTranspose_map {R S : Type*} [CommRing R] [CommRing S]
    (ringMap : R →+* S) (matrix : GL3 R) :
    generalLinearInverseTranspose S (GeneralLinearGroup.map ringMap matrix) =
      GeneralLinearGroup.map ringMap (generalLinearInverseTranspose R matrix) := by
  apply Units.ext
  rfl

theorem generalLinearInverseTranspose_involutive {R : Type*} [CommRing R] (matrix : GL3 R) :
    generalLinearInverseTranspose R (generalLinearInverseTranspose R matrix) = matrix := by
  apply Units.ext
  rfl

noncomputable def realDualHeight (matrix : RealGL3) : ℝ :=
  realPlaneHeight (weyl⁻¹ * generalLinearInverseTranspose ℝ matrix)

noncomputable def integralBinaryDualChange (binary : GeneralLinearGroup (Fin 2) ℤ) : IntegralGL3 :=
  weyl⁻¹ * generalLinearInverseTranspose ℤ (planeLevi binary 1) * weyl

theorem realDualHeight_integral_binary (matrix : RealGL3) (binary : GeneralLinearGroup (Fin 2) ℤ) :
    realDualHeight (integralRealGroup (planeLevi binary 1) * matrix) =
      realPlaneHeight (integralRealGroup (integralBinaryDualChange binary) *
        (weyl⁻¹ * generalLinearInverseTranspose ℝ matrix)) := by
  simp only [realDualHeight, integralBinaryDualChange, map_mul, map_inv,
    integralRealGroup, generalLinearInverseTranspose_map, map_weyl]
  congr 1
  group

theorem integral_binary_dual_height_minimum (matrix : RealGL3) :
    ∃ binary : GeneralLinearGroup (Fin 2) ℤ, ∀ other : GeneralLinearGroup (Fin 2) ℤ,
      realDualHeight (integralRealGroup (planeLevi binary 1) * matrix) ≤
        realDualHeight (integralRealGroup (planeLevi other 1) * matrix) := by
  obtain ⟨integral, integral_member, minimal⟩ := integral_plane_height_minimum
    (weyl⁻¹ * generalLinearInverseTranspose ℝ matrix) (Set.range integralBinaryDualChange)
    (Set.range_nonempty integralBinaryDualChange)
  obtain ⟨binary, rfl⟩ := integral_member
  refine ⟨binary, ?_⟩
  intro other
  simpa only [realDualHeight_integral_binary] using minimal (integralBinaryDualChange other) ⟨other, rfl⟩

end TernaryPeriodPolynomials.EisensteinRegularization.Helpers
