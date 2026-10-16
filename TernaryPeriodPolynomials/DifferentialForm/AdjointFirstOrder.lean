module

public import TernaryPeriodPolynomials.DifferentialForm.LocalAdjoint.Basic
public import TernaryPeriodPolynomials.DifferentialForm.Cutoff
public import TernaryPeriodPolynomials.Analysis.Compact.Weighted.CoefficientRegularity

@[expose] public section


/-! Actual smooth first-order scalar coefficients for the polynomial form codifferential. -/
noncomputable section
namespace TernaryPoly.PolynomialFormCoordinates
open PolynomialFormMetric SymmetricSpaceCharts CompactCoordinateIntegration
open scoped ContDiff Matrix.Norms.Elementwise

def adjointFirstCoefficient (n k : ℕ) (i : Index n k) (t : Index n (k+1))
    (l : Index n k) (j : Index n (k+1)) (d : Fin 5) : Coordinates → ℝ :=
  weightedFirstCoefficient (weightedGram n k) (weightedGram n (k+1)) (differentialCoefficients n k) i t l j d

def adjointZeroCoefficient (n k : ℕ) (i : Index n k) (t : Index n (k+1))
    (l : Index n k) (j : Index n (k+1)) (d : Fin 5) : Coordinates → ℝ :=
  weightedZeroCoefficient (weightedGram n k) (weightedGram n (k+1)) (fun d : Fin 5 => Pi.single d 1)
    (differentialCoefficients n k) (fun _ _ _ _ => 0) i t l j d

/-- Literal components of the genuine adjoint are finite sums of ordinary first-order operators. -/
theorem localAdjoint_firstOrder_expansion (n k : ℕ) (w : Coordinates → FormValue n (k+1))
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (hw : DifferentiableAt ℝ w x) (i : Index n k) :
    components n k (localAdjoint n k w) i x =
      ∑ l, ∑ j, ∑ d : Fin 5, ∑ t, firstOrder (Pi.single d 1)
        (adjointFirstCoefficient n k i t l j d) (adjointZeroCoefficient n k i t l j d)
        (components n (k+1) w t) x := by
  rw [components_localAdjoint]
  apply weightedMatrixAdjoint_firstOrder_expansion
  · intros; exact differentiableAt_const _
  · intro j t
    have h := contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n (k+1)) j) t
    exact h.differentiableOn (by simp) x hx |>.differentiableAt (isOpen_positiveCoordinates.mem_nhds hx)
  · exact differentiableAt_components n (k+1) hw

/-- The principal adjoint coefficients are genuinely smooth throughout the true coordinate domain. -/
theorem contDiffOn_adjointFirstCoefficient (n k : ℕ) (i : Index n k) (t : Index n (k+1))
    (l : Index n k) (j : Index n (k+1)) (d : Fin 5) :
    ContDiffOn ℝ ∞ (adjointFirstCoefficient n k i t l j d) positiveCoordinates := by
  apply contDiffOn_weightedFirstCoefficient
  · intro i l
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram_inverse n k) i) l
  · intro j t
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n (k+1)) j) t
  · intros; exact contDiffOn_const

/-- All zeroth adjoint coefficients, including the differentiated metric, are actually smooth. -/
theorem contDiffOn_adjointZeroCoefficient (n k : ℕ) (i : Index n k) (t : Index n (k+1))
    (l : Index n k) (j : Index n (k+1)) (d : Fin 5) :
    ContDiffOn ℝ ∞ (adjointZeroCoefficient n k i t l j d) positiveCoordinates := by
  apply contDiffOn_weightedZeroCoefficient isOpen_positiveCoordinates
  · intro i l
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram_inverse n k) i) l
  · intro j t
    exact contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_weightedGram n (k+1)) j) t
  · intros; exact contDiffOn_const
  · intros; exact contDiffOn_const

end TernaryPoly.PolynomialFormCoordinates
