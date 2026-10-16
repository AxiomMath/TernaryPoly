module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothPairingAlgebra
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.IntegralBilinear

@[expose] public section

/-! The actual quotient Riemannian current of a genuine local smooth equivariant form. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric SymmetricSpaceCovering SymmetricSpaceRiemannian
  SmoothCoveringDeRham
open scoped SymmetricSpaceRiemannian

/-- Every genuine local smooth equivariant form defines an intrinsic local current by literal
integration of its genuine quotient metric pairing with actual supported compact tests. -/
def intrinsicSmoothCurrent (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U) :
    EquivariantForm (deckRepresentation n) U k →ₗ[ℝ] IntrinsicCurrent n k U :=
  integrableBilinearIntegral
    (A := EquivariantForm (deckRepresentation n) U k) (B := supportedCompactCore n k U)
    orbitVolume (intrinsicSmoothPairingLinear n k U)
    (intrinsicSmoothPairing_integrable n k U hU)

@[simp] theorem intrinsicSmoothCurrent_apply (n k : ℕ) (U : Set OrbitSpace) (hU : IsOpen U)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) :
    intrinsicSmoothCurrent n k U hU a w = ∫ q, intrinsicSmoothPairing n k U a w q ∂orbitVolume := rfl

end TernaryPoly.PolynomialFormWeakSmooth
