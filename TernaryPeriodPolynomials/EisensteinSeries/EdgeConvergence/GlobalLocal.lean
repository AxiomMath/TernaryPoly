module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Hilbert

@[expose] public section


/-!
# The global Hilbert standard integral as a multiple of the local one

If integrating the plane cusp lift over the opposite radical away from `∞` and `3` multiplies the
vector at the local standard argument by a scalar `lam`, then in the half plane of absolute
convergence the global standard integral is `lam` times the local standard integral.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

/-- The inner integral of the global standard integral, over the coordinates away from `∞` and `3`,
for a fixed local coordinate. -/
def awayIntegral {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (localParameter : LocalLine × LocalLine) : data.cusp.H :=
  ∫ away, (CuspLift.vector data .plane parameter function induced
    (awayOpposite away * (weyl⁻¹ * localRadical localParameter * argument))).val
      ∂awayRadicalMeasure

/-- In the half plane of absolute convergence, the global Hilbert standard integral is the scalar
times the local one as soon as the away integral is that scalar times the local integrand. -/
theorem standardValue_eq_smul_localValue {degree : ℕ} (data : InducingData degree)
    (parameter : ℂ) (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (halfPlane : -(degree : ℝ) / 2 < parameter.re) (argument : AdelicGL) (lam : ℂ)
    (compression : ∀ localParameter : LocalLine × LocalLine,
      awayIntegral data parameter function induced argument localParameter =
        lam • localIntegrand data parameter function induced argument localParameter) :
    HilbertStandard.value data parameter function induced argument =
      lam • localValue data parameter function induced argument := by
  unfold HilbertStandard.value
  rw [radicalIntegral_local_fubini _
    (HilbertStandard.integrand_integrable data parameter function induced halfPlane argument)]
  unfold localValue
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun localParameter => ?_)
  beta_reduce
  rw [← compression localParameter]
  unfold awayIntegral
  refine integral_congr_ae (Filter.Eventually.of_forall fun away => ?_)
  exact congrArg (fun y => (CuspLift.vector data .plane parameter function induced y).val)
    (standard_argument_join localParameter away argument)

end TernaryPeriodPolynomials.EdgeConvergence
