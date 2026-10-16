module

public import TernaryPeriodPolynomials.EisensteinSeries.PlaneContinuation.Cusp.Vectors

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.PlaneEisensteinContinuation.Central

theorem normPower_pow (t : Adelesˣ) (m : ℕ) (z : ℂ) :
    normPower (t ^ m) z = normPower t ((m : ℂ) * z) := by
  induction m with
  | zero => simp [TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_one, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_zero]
  | succ m inductionHypothesis =>
    rw [pow_succ, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_mul, inductionHypothesis,
      ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_add]
    congr 1
    push_cast
    ring

theorem scalar_planeLevi (t : Adelesˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) t =
      planeLevi (Matrix.GeneralLinearGroup.scalar (Fin 2) t) t := by
  apply Units.ext
  apply Matrix.ext
  intro row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar, planeLevi, planeBlock,
      Matrix.diagonal]

theorem induced_binaryScalar {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (t : Adelesˣ) (g : AdelicGL) :
    f (planeLevi (Matrix.GeneralLinearGroup.scalar (Fin 2) t) 1 * g) =
      normPower t (2 * binaryInductionExponent n .plane s) *
        D.cusp.centralCharacter t * f g := by
  rw [TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.induced_eq_planeCuspVector hf,
    Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, normPower_pow]
  have hcentral := D.cusp.central t
    (TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.planeCuspVector hf g) 1
  rw [mul_one] at hcentral
  rw [hcentral, ← TernaryPeriodPolynomials.PlaneEisensteinContinuation.CuspVectors.induced_eq_planeCuspVector_one hf g,
    ← mul_assoc]
  norm_num

theorem induced_central {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (t : Adelesˣ) (g : AdelicGL) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 3) t * g) =
      (D.chi.toMonoidHom t * D.cusp.centralCharacter t *
        normPower t ((n : ℂ) + 3)) * f g := by
  rw [scalar_planeLevi, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.induced_planeLevi_scalar hf,
    induced_binaryScalar hf]
  have hexponent : -2 * inductionExponent .plane s +
      2 * binaryInductionExponent n .plane s = (n : ℂ) + 3 := by
    simp only [binaryInductionExponent]
    ring
  rw [← hexponent, TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.normPower_add]
  ring

theorem norm_induced_central {n : ℕ} {D : InducingData n} {s : ℂ}
    {f : AdelicGL → ℂ} (hf : IsInduced D .plane s f)
    (t : Adelesˣ) (g : AdelicGL) :
    ‖f (Matrix.GeneralLinearGroup.scalar (Fin 3) t * g)‖ =
      Real.exp (((n : ℝ) + 3) * Real.log (adeleNorm t : ℝ)) * ‖f g‖ := by
  rw [induced_central hf, norm_mul, norm_mul, norm_mul,
    D.chi.unitary, D.cusp.centralUnitary, one_mul, one_mul,
    TernaryPeriodPolynomials.PlaneEisensteinContinuation.Helpers.norm_normPower]
  simp

end TernaryPeriodPolynomials.PlaneEisensteinContinuation.Central
