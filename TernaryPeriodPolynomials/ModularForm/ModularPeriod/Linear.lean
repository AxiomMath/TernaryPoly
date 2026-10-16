module

public import TernaryPeriodPolynomials.ModularForm.Period.Basic

@[expose] public section


noncomputable section
open Complex MvPolynomial
open UpperHalfPlane hiding I

namespace TernaryPoly.BinaryCuspPeriod

/-- Actual cusp Mellin moments are additive, since both integrals converge. -/
theorem moment_add {d : ℕ} (f g : Forms d) (s : ℂ) :
    moment (f+g) s = moment f s + moment g s := by
  exact (hasMellin_add (moment_convergent f s) (moment_convergent g s)).2

/-- Actual cusp Mellin moments commute with complex scalar multiplication. -/
theorem moment_smul {d : ℕ} (f : Forms d) (c s : ℂ) :
    moment (c • f) s = c * moment f s := by
  exact mellin_const_smul (fun t : ℝ => f (ofComplex (I*t))) s c

/-- Every finite binomial/Mellin coefficient is additive in the cusp form. -/
theorem periodCoefficient_add {d : ℕ} (f g : Forms d) (j : ℕ) :
    periodCoefficient (f+g) j = periodCoefficient f j + periodCoefficient g j := by
  simp only [periodCoefficient, moment_add, mul_add]

/-- Every finite binomial/Mellin coefficient is complex-linear in the cusp form. -/
theorem periodCoefficient_smul {d : ℕ} (f : Forms d) (c : ℂ) (j : ℕ) :
    periodCoefficient (c • f) j = c * periodCoefficient f j := by
  simp only [periodCoefficient, moment_smul]
  ring

theorem period_add {d : ℕ} (f g : Forms d) : period (f+g) = period f + period g := by
  classical
  simp only [period, periodCoefficient_add, map_add, Finset.sum_add_distrib]

theorem period_smul {d : ℕ} (f : Forms d) (c : ℂ) : period (c • f) = c • period f := by
  classical
  simp only [period, periodCoefficient_smul, Finset.smul_sum, smul_monomial, smul_eq_mul]

theorem oddPeriod_add {d : ℕ} (f g : Forms d) : oddPeriod (f+g) = oddPeriod f + oddPeriod g := by
  classical
  simp only [oddPeriod, periodCoefficient_add, map_add, Finset.sum_add_distrib]

theorem oddPeriod_smul {d : ℕ} (f : Forms d) (c : ℂ) :
    oddPeriod (c • f) = c • oddPeriod f := by
  classical
  simp only [oddPeriod, periodCoefficient_smul, Finset.smul_sum, smul_monomial, smul_eq_mul]

/-- The actual full period polynomial as a complex-linear map. -/
def periodLinearMap (d : ℕ) : Forms d →ₗ[ℂ] MvPolynomial (Fin 2) ℂ where
  toFun := period
  map_add' := period_add
  map_smul' := fun c f => period_smul f c

/-- The actual odd period polynomial as a complex-linear map. -/
def oddPeriodLinearMap (d : ℕ) : Forms d →ₗ[ℂ] MvPolynomial (Fin 2) ℂ where
  toFun := oddPeriod
  map_add' := oddPeriod_add
  map_smul' := fun c f => oddPeriod_smul f c

end TernaryPoly.BinaryCuspPeriod
