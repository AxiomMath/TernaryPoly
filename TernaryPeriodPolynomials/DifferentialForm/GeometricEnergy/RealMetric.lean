module

public import TernaryPeriodPolynomials.DifferentialForm.GeometricEnergy.BaseEnergy
public import TernaryPeriodPolynomials.DifferentialForm.Connection.RealFrame

@[expose] public section

/-! Actual metric transport by determinant-normalized real congruences. -/
noncomputable section
namespace TernaryPoly.PolynomialFormGeometricEnergy
open Matrix SL3PolynomialCoercivity PolynomialCoefficientMetric PolynomialFormMetric PolynomialFormConnection
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering
open SymmetricSpaceTraceMetric SymmetricSpaceRiemannian SmoothCoveringDeRham
open scoped Matrix.Norms.Elementwise

theorem coordinateGram_real (g : RealGL) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    (LinearMap.toMatrix' (fderiv ℝ (coordinateAction g) x).toLinearMap).transpose *
      coordinateGram (coordinateAction g x) *
        LinearMap.toMatrix' (fderiv ℝ (coordinateAction g) x).toLinearMap = coordinateGram x := by
  let L := (fderiv ℝ (coordinateAction g) x).toLinearMap
  have h : LinearMap.BilinForm.comp (coordinateBilin (coordinateAction g x)) L L = coordinateBilin x := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact coordinatePair_fderiv_invariant g x hx v w
  have hm := congrArg LinearMap.BilinForm.toMatrix' h
  simpa only [LinearMap.BilinForm.toMatrix'_comp, coordinateGram, L] using hm

theorem inverseGram_real (g : RealGL) (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    LinearMap.toMatrix' (fderiv ℝ (coordinateAction g) x).toLinearMap * inverseGram x *
      (LinearMap.toMatrix' (fderiv ℝ (coordinateAction g) x).toLinearMap).transpose =
        inverseGram (coordinateAction g x) :=
  inverse_congruence _ _ _ (coordinateGram_posDef x hx) (coordinateGram_real g x hx)

theorem coordinateCoefficientBilin_real (n : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (p q : Coefficients n) :
    coordinateCoefficientBilin n (coordinateAction g x) (realCoefficientMap n g p) (realCoefficientMap n g q) =
      coordinateCoefficientBilin n x p q := by
  change matrixPairing (coordinateForm (coordinateAction g x))
    (realSubstitute g.val⁻¹ p.val) (realSubstitute g.val⁻¹ q.val) = matrixPairing (coordinateForm x) p.val q.val
  rw [coordinateForm_real g hg x hx]
  have h := matrixPairing_congruence g (coordinateForm x) p.val q.val
  have hs : star g.val = g.val.transpose := rfl
  simpa only [conjugate, hs, Matrix.coe_units_inv] using h

/-- Actual tangent pullback and literal inverse substitution preserve the form pairing. -/
theorem formPairing_real (n k : ℕ) (g : RealGL) (hg : g.val.det ^ 2 = 1)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) (a b c d : FormValue n k)
    (ha : a.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k c)
    (hb : b.compContinuousLinearMap (fderiv ℝ (coordinateAction g) x) =
      coefficientFormMap (realCoefficientMap n g) k d) :
    formPairing n k (coordinateAction g x) a b = formPairing n k x c d := by
  unfold formPairing
  apply congrArg ((k.factorial : ℝ)⁻¹ * ·)
  unfold inverseGram
  rw [← contraction_isometry (coordinateCoefficientBilin n (coordinateAction g x))
    (coordinateGram x) (coordinateGram (coordinateAction g x)) (coordinateGram_posDef x hx)
    (fderiv ℝ (coordinateAction g) x) (coordinateGram_real g x hx) a b, ha, hb]
  unfold matrixContraction
  apply Finset.sum_congr rfl
  intro I _
  apply Finset.sum_congr rfl
  intro J _
  apply congrArg (tensorMatrix k (inverseGram x) I J * ·)
  exact coordinateCoefficientBilin_real n g hg x hx (formCoordinates c I) (formCoordinates d J)

end TernaryPoly.PolynomialFormGeometricEnergy
