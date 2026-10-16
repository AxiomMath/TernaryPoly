module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.Divergence.Algebra
public import TernaryPeriodPolynomials.DifferentialForm.Connection.ContractionTensor

@[expose] public section

/-! Differentiation of the actual inverse-metric dual and its genuine weighted divergence. -/
noncomputable section
namespace TernaryPoly.PolynomialFormConnection
open Matrix PolynomialFormMetric SymmetricSpaceCharts
open scoped Matrix.Norms.Elementwise

/-- Coordinate inverse-metric dual of a coordinate covector field. -/
def metricDualCovector (a : Coordinates → Coordinates) (x : Coordinates) : Coordinates :=
  fun i => ∑ j, inverseGram x i j * a x j

theorem differentiableAt_metricDualCovector (a : Coordinates → Coordinates) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (ha : DifferentiableAt ℝ a x) :
    DifferentiableAt ℝ (metricDualCovector a) x := by
  apply differentiableAt_pi.mpr
  intro i
  apply DifferentiableAt.fun_sum
  intro j _
  exact (differentiableAt_inverseGram_entry x hx i j).mul (differentiableAt_pi.mp ha j)

theorem fderiv_metricDualCovector (a : Coordinates → Coordinates) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (ha : DifferentiableAt ℝ a x) (u : Coordinates) (i : Fin 5) :
    fderiv ℝ (metricDualCovector a) x u i =
      ∑ j, ((fderiv ℝ inverseGram x u i j) * a x j + inverseGram x i j * fderiv ℝ a x u j) := by
  have hd := differentiableAt_metricDualCovector a x hx ha
  have he := congrArg (fun L => L u) (fderiv_apply hd i)
  change fderiv ℝ (fun y => ∑ j, inverseGram y i j * a y j) x u =
    fderiv ℝ (metricDualCovector a) x u i at he
  rw [← he]
  have hprod (j : Fin 5) := (differentiableAt_inverseGram_entry x hx i j).mul (differentiableAt_pi.mp ha j)
  have hsum : fderiv ℝ (fun y => ∑ j, inverseGram y i j * a y j) x =
      ∑ j, fderiv ℝ (fun y => inverseGram y i j * a y j) x := by
    convert! fderiv_fun_sum (𝕜 := ℝ) (A := fun j y => inverseGram y i j * a y j)
      (x := x) (u := Finset.univ) (fun j _ => hprod j) using 1
  rw [hsum]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (differentiableAt_inverseGram_entry x hx i j) (differentiableAt_pi.mp ha j)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, fderiv_inverseGram_entry x hx u]
  rw [fderiv_apply ha j]
  change inverseGram x i j * fderiv ℝ a x u j + a x j * fderiv ℝ inverseGram x u i j = _
  ring

theorem tangentConnectionMatrix_symmetric (x : Coordinates) (hx : x ∈ positiveCoordinates)
    (i r j : Fin 5) :
    tangentConnectionMatrix x (Pi.single i 1) r j = tangentConnectionMatrix x (Pi.single j 1) r i := by
  change tangentConnection x (Pi.single i 1) (Pi.single j 1) r =
    tangentConnection x (Pi.single j 1) (Pi.single i 1) r
  rw [tangentConnection_symmetric x hx]

theorem weightedDivergence_metricDualCovector (a : Coordinates → Coordinates) (x : Coordinates)
    (hx : x ∈ positiveCoordinates) (ha : DifferentiableAt ℝ a x) (b : Fin 5 → Fin 5 → ℝ)
    (hb : ∀ i j, fderiv ℝ a x (Pi.single i 1) j =
      b i j + ∑ r, tangentConnectionMatrix x (Pi.single i 1) r j * a x r) :
    weightedDivergence (metricDualCovector a) x = ∑ i, ∑ j, inverseGram x i j * b i j := by
  rw [weightedDivergence_expansion _ x hx (differentiableAt_metricDualCovector a x hx ha)]
  simp only [fderiv_metricDualCovector a x hx ha, inverseGramDerivative x hx, hb, metricDualCovector]
  exact divergence_metric_dual_algebra (inverseGram x) (fun i => tangentConnectionMatrix x (Pi.single i 1))
    (a x) b (tangentConnectionMatrix_symmetric x hx)

end TernaryPoly.PolynomialFormConnection
