module

public import TernaryPeriodPolynomials.ModularForm.ThreeTerm.Basic

@[expose] public section


noncomputable section
open MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- Every actual full-level cusp form belongs to the formerly conditional three-term kernel. -/
theorem threeTermKernel_eq_top {d : ℕ} (hd : Even d) : threeTermKernel d = ⊤ := by
  apply top_unique
  intro f _
  exact threeTermDefect_eq_zero hd f

/-- The unrestricted actual cusp-to-odd-period linear map, with its analytic three-term gate closed. -/
def periodMap (d : ℕ) (hd : Even d) : Forms d →ₗ[ℂ] BinaryComplexPeriod.space ℂ d :=
  periodMapOfThreeTerm d hd (threeTermDefect_eq_zero hd)

/-- The unrestricted map is literally the finite odd Mellin polynomial. -/
@[simp] theorem periodMap_coe (d : ℕ) (hd : Even d) (f : Forms d) :
    (periodMap d hd f : MvPolynomial (Fin 2) ℂ) = oddPeriod f := rfl

/-- The actual map has exactly the proved outer-coefficient normalization. -/
theorem extreme_periodMap (d : ℕ) (hd : Even d) (f : Forms d) :
    BinaryComplexPeriod.extreme ℂ d (periodMap d hd f) = (oddPeriod f).coeff (exponent d 1) := rfl

end TernaryPoly.BinaryCuspPeriod
