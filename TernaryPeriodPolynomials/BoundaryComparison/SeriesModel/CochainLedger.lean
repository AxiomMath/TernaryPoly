module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.ChartAgreement
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CochainEntry

@[expose] public section


/-!
# The scalar ledger of the holomorphic half of `cOmega`

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix Set MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument.Statements.RealEntrySeed
  TernaryPeriodPolynomials.Argument GeneralEisenstein GeneralEisenstein.Adelic
  TernaryPeriodPolynomials.SourceConstruction

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem seedForm_const_mul (n : ℕ) (K : ℂ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (i j : Fin 5) :
    seedForm n (fun z => K * h z) p i j = MvPolynomial.C K * seedForm n h p i j := by
  unfold seedForm
  rw [← mul_assoc, ← MvPolynomial.C_mul]
  congr 2
  ring

theorem formPair_seed_const_mul (n : ℕ) (K : ℂ) (h : ℂ → ℂ) (G Q₁ Q₂ : Mat3) :
    formPair (seedForm n (fun z => K * h z)) G Q₁ Q₂ = MvPolynomial.C K * formPair (seedForm n h) G Q₁ Q₂ := by
  unfold formPair
  simp only [seedForm_const_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `planeIntG` is linear in the holomorphic datum `h`: a constant factor comes out. -/
theorem planeIntG_const_mul (n : ℕ) (K : ℂ) (h : ℂ → ℂ) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    planeIntG n (fun z => K * h z) M Γ₀ Γ₁ Γ₂ κ = K * planeIntG n h M Γ₀ Γ₁ Γ₂ κ := by
  unfold planeIntG twPull
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [formPair_seed_const_mul, ConvergenceC4.rho_C_mul, MvPolynomial.coeff_C_mul]

/-- **Scalar ledger of the holomorphic half**: the plane datum `h = (-1)ⁿ (n+1) c_F(g) · ½ F(x · b_F(g))` of `cOmega` pulls the scalar
`(-1)ⁿ (n+1) c_F(g) / 2` out of the seed integral; what remains is the seed integral of the scalar function `F(x · b_F(g))`. -/
theorem planeIntG_planeHolData (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (g : AdelicGL)
    (x : BinaryAdelicGL) (M Γ₀ Γ₁ Γ₂ : Mat3) (κ : Fin 3 →₀ ℕ) :
    planeIntG n (planeHolData n D F g x) M Γ₀ Γ₁ Γ₂ κ =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D g) * planeIntG n (F (x * bF g)) M Γ₀ Γ₁ Γ₂ κ := by
  have e : planeHolData n D F g x = fun z => (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D g) * F (x * bF g) z := by
    rw [planeHolData_eq]; funext z; ring
  rw [e]
  exact planeIntG_const_mul n _ (F (x * bF g)) M Γ₀ Γ₁ Γ₂ κ

/-- **`cOmega` as two seed integrals** (holomorphic part at `g_∞` and the `J`-reflected part at `ε g_∞`), with the common scalar
`K_g = (-1)ⁿ (n+1) c_F(g) / 2` pulled out. -/
theorem cOmegaCoeff_eq (n : ℕ) (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ) (y : Fin 3 → RealGL3)
    (g : AdelicGL) (κ : Fin 3 →₀ ℕ) :
    cOmegaCoeff n D F y g κ =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D g) *
        (planeIntG n (F (1 * bF g)) (realGroup g).val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ +
         planeIntG n (F (atInfinity UpperHalfPlane.J * bF g)) (epsJ.val * (realGroup g).val)
           (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ) := by
  unfold cOmegaCoeff
  rw [planeIntG_planeHolData, planeIntG_planeHolData]
  ring

end TernaryPeriodPolynomials.Argument.FormSeriesModel
