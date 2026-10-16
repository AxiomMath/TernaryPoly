module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.RadicalDeriv
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Eichler.Regular

@[expose] public section


/-!
# Linear combinations of radical coefficients

The coordinates `pointCoord n z j` of the binary point power in the weight basis, and the identity
`∑ j, pointCoord n z j · D(coeff_m R(basis j)) = D(coeff_m R(Q_z))` expressed through
`hasFDerivAt_radicalCoeff_pointPower` (`sum_fderiv_radicalCoeff`): the derivative of the radical on a point power
is the weighted sum of the derivatives on the basis forms.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

/-- The coordinates of the binary point power in the weight basis. -/
def pointCoord (n : ℕ) (z : ℂ) (j : Fin (n + 2)) : ℂ :=
  (binaryWeightBasis (n + 1)).coord j (binaryPointPower (n + 1) z)

theorem sum_pointCoord_smul (n : ℕ) (z : ℂ) :
    ∑ j, pointCoord n z j • binaryWeightBasis (n + 1) j = binaryPointPower (n + 1) z := by
  simp only [pointCoord, Module.Basis.coord_apply]
  exact Module.Basis.sum_repr _ _

theorem radicalCoeff_sum_smul (n : ℕ) (c : Fin (n + 2) → ℂ) (m : Fin 3 →₀ ℕ) (st : ℝ × ℝ) :
    radicalCoeff n (∑ j, c j • binaryWeightBasis (n + 1) j) m st =
      ∑ j, c j * radicalCoeff n (binaryWeightBasis (n + 1) j) m st := by
  unfold radicalCoeff
  simp only [map_sum, map_smul]
  rw [← Finset.sum_sub_distrib, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_sub, MvPolynomial.coeff_smul, smul_eq_mul]

theorem differentiableAt_radicalCoeff (n : ℕ) (Q : Binary.HomogeneousPoly (n + 1)) (m : Fin 3 →₀ ℕ)
    (st : ℝ × ℝ) : DifferentiableAt ℝ (radicalCoeff n Q m) st :=
  ((contDiff_radicalCoeff n Q m).differentiable (by simp)).differentiableAt

theorem sum_fderiv_radicalCoeff (n : ℕ) (z : ℂ) (m : Fin 3 →₀ ℕ) (st : ℝ × ℝ) (v : ℝ × ℝ) :
    ∑ j, pointCoord n z j * fderiv ℝ (radicalCoeff n (binaryWeightBasis (n + 1) j) m) st v =
      radLin (-((n + 1 : ℕ) : ℂ) * ((pointPowerTernary z -
        MvPolynomial.C ((st.1 : ℂ) - z * (st.2 : ℂ)) * MvPolynomial.X 2) ^ n).coeff m) z v := by
  have hfun : radicalCoeff n (binaryPointPower (n + 1) z) m =
      fun st => ∑ j, pointCoord n z j * radicalCoeff n (binaryWeightBasis (n + 1) j) m st := by
    funext st
    rw [← sum_pointCoord_smul n z, radicalCoeff_sum_smul]
  have h1 : fderiv ℝ (radicalCoeff n (binaryPointPower (n + 1) z) m) st =
      ∑ j, pointCoord n z j • fderiv ℝ (radicalCoeff n (binaryWeightBasis (n + 1) j) m) st := by
    rw [hfun]
    rw [fderiv_fun_sum (fun j _ => ((differentiableAt_radicalCoeff n _ m st).const_mul _))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fderiv_const_mul (differentiableAt_radicalCoeff n _ m st)]
  have h2 := (hasFDerivAt_radicalCoeff_pointPower n z m st).fderiv
  rw [h1] at h2
  have h3 := congrArg (fun L => L v) h2
  simpa [sum_apply] using h3

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
