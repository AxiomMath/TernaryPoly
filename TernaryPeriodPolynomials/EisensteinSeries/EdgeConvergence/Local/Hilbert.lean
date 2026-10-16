module

public import TernaryPeriodPolynomials.EisensteinSeries.EdgeConvergence.Local.Coordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.StandardConstruction.Hilbert.FullRealization
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Adelic.ThreeSplitting

@[expose] public section


/-!
# The local Hilbert standard integral at `{∞, 3}`

For a plane-induced section `f` at the parameter `s`, the plane cusp lift `v_s(y) ∈ H` of `f` at `y`
is `CuspLift.vector`. The local standard integral integrates `v_s(w⁻¹ n(u) g)` only over the line
radical coordinates `u ∈ (ℝ × ℚ₃)²` at the places `∞` and `3`. The full standard integral factors
through the local one: the line radical element with coordinates `u + u'`, `u'` away from `∞` and `3`,
is `w⁻¹ n(u + u') = n⁻(u') w⁻¹ n(u)` with `n⁻ = lowerPlaneUnipotent`.
-/

open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction

noncomputable section

namespace TernaryPeriodPolynomials.EdgeConvergence

theorem localAdele_continuous : Continuous localAdele :=
  continuous_fst.prodMk (finiteAtThreeScalar_continuous.comp continuous_snd)

theorem localRadical_continuous : Continuous localRadical :=
  InducedContinuity.lineUnipotent_continuous.comp
    ((localAdele_continuous.comp continuous_fst).prodMk (localAdele_continuous.comp continuous_snd))

/-- The integrand of the local standard integral. -/
def localIntegrand {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) (coordinates : LocalLine × LocalLine) : data.cusp.H :=
  (CuspLift.vector data .plane parameter function induced
    (weyl⁻¹ * localRadical coordinates * argument)).val

theorem localIntegrand_continuous {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) :
    Continuous (localIntegrand data parameter function induced argument) :=
  (CuspLift.continuous data .plane parameter function induced).comp
    ((continuous_const.mul localRadical_continuous).mul continuous_const)

/-- The local standard integral at the places `∞` and `3`. -/
def localValue {degree : ℕ} (data : InducingData degree) (parameter : ℂ)
    (function : AdelicGL → ℂ) (induced : IsInduced data .plane parameter function)
    (argument : AdelicGL) : data.cusp.H :=
  ∫ coordinates, localIntegrand data parameter function induced argument coordinates
    ∂localRadicalMeasure

/-- The opposite plane radical element with coordinates away from `∞` and `3`. -/
def awayOpposite (coordinates : FiniteAwayThree × FiniteAwayThree) : AdelicGL :=
  lowerPlaneUnipotent (awayAdele coordinates.1) (awayAdele coordinates.2)

theorem weyl_inverse_lineUnipotent {R : Type*} [CommRing R] (first second : R) :
    (weyl⁻¹ : GL3 R) * lineUnipotent first second =
      lowerPlaneUnipotent first second * weyl⁻¹ := by
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [weyl, lowerPlaneUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The global standard integrand at the joined coordinates. -/
theorem standard_argument_join (localParameter : LocalLine × LocalLine)
    (away : FiniteAwayThree × FiniteAwayThree) (argument : AdelicGL) :
    weyl⁻¹ * lineUnipotent (radicalLocalAwayJoin (localParameter, away)).1
        (radicalLocalAwayJoin (localParameter, away)).2 * argument =
      awayOpposite away * (weyl⁻¹ * localRadical localParameter * argument) := by
  rw [radicalLocalAwayJoin_apply]
  simp only
  rw [add_comm (localAdele localParameter.1), add_comm (localAdele localParameter.2),
    lineUnipotent_add, ← mul_assoc, ← mul_assoc, weyl_inverse_lineUnipotent]
  simp only [awayOpposite, localRadical, mul_assoc]

end TernaryPeriodPolynomials.EdgeConvergence
