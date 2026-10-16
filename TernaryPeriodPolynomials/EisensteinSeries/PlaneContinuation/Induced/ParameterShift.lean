module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.ParameterShiftHeight

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.PlaneEisensteinContinuation.ParameterShiftHeight TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors TernaryPeriodPolynomials.PlaneEisensteinContinuation.GodementIntegral
open scoped Matrix.Norms.Elementwise

noncomputable section

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedParameterShift

def function (source target : ℂ) (value : AdelicGL → ℂ) (point : AdelicGL) : ℂ :=
  coefficient (target - source) point * value point

theorem cusp_factor (degree : ℕ) (source target : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane target) *
      coefficient (target - source) (planeLevi binary 1 * point) =
        coefficient (target - source) point * normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane source) := by
  rw [coefficient_levi, Helpers.normPower_one, mul_one, ← mul_assoc, ← Helpers.normPower_add]
  have exponent : -binaryInductionExponent degree .plane target + (target - source) / 3 =
      -binaryInductionExponent degree .plane source := by simp only [binaryInductionExponent, inductionExponent]; ring
  rw [exponent, mul_comm]

theorem outer_shift {degree : ℕ} (data : InducingData degree) (source target : ℂ) (scalar : Adelesˣ) :
    outerCharacter data target scalar = normPower scalar (-2 * (target - source) / 3) * outerCharacter data source scalar := by
  change data.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane target) = _
  have exponent : -2 * inductionExponent .plane target =
      -2 * (target - source) / 3 + -2 * inductionExponent .plane source := by simp only [inductionExponent]; ring
  rw [exponent, Helpers.normPower_add]
  change _ = normPower scalar (-2 * (target - source) / 3) *
    (data.chi.toMonoidHom scalar * normPower scalar (-2 * inductionExponent .plane source))
  ring

theorem level_compact (matrix : finiteLevel) : inMaximalCompact (atFinite matrix.val) := by
  obtain ⟨integer, _, equality⟩ := matrix.property
  exact MaximalCompact.finiteCompact_atFinite ⟨matrix.val, integer, equality⟩

theorem realize_shift {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (induced : IsInduced data .plane source value) (target : ℂ) (point : AdelicGL) (binary : BinaryAdelicGL) :
    data.cusp.realize (coefficient (target - source) point • planeCuspVector induced point) binary =
      normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane target) *
        function source target value (planeLevi binary 1 * point) := by
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, realize_planeCuspVector, function]
  simp only [← mul_assoc, cusp_factor]

theorem smooth_lift {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (induced : IsInduced data .plane source value) (target : ℂ) :
    HasSmoothCuspLift data .plane target (fun _ : Fin 0 → RealGL3 => function source target value) := by
  intro point
  obtain ⟨lift, smooth, equality⟩ := induced.2.2.1 point
  refine ⟨fun matrices => coefficient (target - source) (point * atInfinity (matrices 0)) • lift matrices,
    (coefficient_smooth (target - source) point).smul smooth, ?_⟩
  intro matrices binary
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, equality, function, Fin.last_zero, binaryLevi]
  rw [← mul_assoc (normPower (GeneralLinearGroup.det binary) (-binaryInductionExponent degree .plane target)), cusp_factor]
  ring

theorem induced {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (original : IsInduced data .plane source value) (target : ℂ) :
    IsInduced data .plane target (function source target value) := by
  refine ⟨fun point => (coefficient_smooth (target - source) point).mul (original.1 point), ?_,
    smooth_lift original target, ?_, ?_, ?_⟩
  · intro matrix point
    rw [function, coefficient_compact (target - source) point _ (level_compact matrix), original.2.1]
    rfl
  · intro first second point
    rw [function, coefficient_unipotent, original.2.2.2.1]
    rfl
  · intro scalar point
    change function source target value (planeLevi 1 scalar * point) = outerCharacter data target scalar * function source target value point
    rw [function, coefficient_levi, map_one, Helpers.normPower_one, one_mul, original.2.2.2.2.1, outer_shift, function]
    change (normPower scalar (-2 * (target - source) / 3) * coefficient (target - source) point) *
      (outerCharacter data source scalar * value point) = _
    ring
  · intro point
    refine ⟨coefficient (target - source) point • planeCuspVector original point, ?_⟩
    funext binary
    exact realize_shift original target point binary

theorem cuspVector {degree : ℕ} {data : InducingData degree} {source : ℂ} {value : AdelicGL → ℂ}
    (original : IsInduced data .plane source value) (target : ℂ) (point : AdelicGL) :
    planeCuspVector (induced original target) point = coefficient (target - source) point • planeCuspVector original point := by
  apply planeCuspVector_unique
  intro binary
  exact realize_shift original target point binary

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.InducedParameterShift
