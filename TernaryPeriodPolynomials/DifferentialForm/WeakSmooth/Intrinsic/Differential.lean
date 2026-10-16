module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.Tests
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Test.DualAlgebra

@[expose] public section


/-! Intrinsic local current differentiation, using the actual support-preserving compact adjoint. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialFormCoordinates PolynomialFormHilbert SymmetricSpaceCovering SmoothCoveringDeRham

/-- The genuine formal adjoint restricts to every actual supported compact test space. -/
def supportedCompactAdjoint (n k : ℕ) (U : Set OrbitSpace) :
    supportedCompactCore n (k+1) U →ₗ[ℝ] supportedCompactCore n k U where
  toFun w := ⟨compactAdjoint n k w.val,
    (quotientSupport_equivariantAdjoint n k w.val.val).trans w.property⟩
  map_add' w z := Subtype.ext (map_add (compactAdjoint n k) w.val z.val)
  map_smul' c w := Subtype.ext (map_smul (compactAdjoint n k) c w.val)

/-- The actual local current differential is the transpose of the actual compact formal adjoint. -/
def intrinsicCurrentDifferential (n k : ℕ) (U : Set OrbitSpace) :
    IntrinsicCurrent n k U →ₗ[ℝ] IntrinsicCurrent n (k+1) U :=
  (supportedCompactAdjoint n k U).dualMap

/-- Actual local weak exterior differentiation squares to zero. -/
theorem intrinsicCurrentDifferential_squared (n k : ℕ) (U : Set OrbitSpace)
    (T : IntrinsicCurrent n k U) :
    intrinsicCurrentDifferential n (k+1) U (intrinsicCurrentDifferential n k U T) = 0 := by
  apply LinearMap.ext
  intro w
  change T (supportedCompactAdjoint n k U (supportedCompactAdjoint n (k+1) U w)) = 0
  have hz : supportedCompactAdjoint n k U (supportedCompactAdjoint n (k+1) U w) = 0 :=
    Subtype.ext (compactAdjoint_squared n k w.val)
  exact (congrArg T hz).trans (map_zero T)

/-- The intrinsic current differential commutes with actual quotient-open restriction. -/
theorem intrinsicCurrentRestriction_differential (n k : ℕ) {U V : Set OrbitSpace}
    (hVU : V ⊆ U) (T : IntrinsicCurrent n k U) :
    intrinsicCurrentRestriction n (k+1) hVU (intrinsicCurrentDifferential n k U T) =
      intrinsicCurrentDifferential n k V (intrinsicCurrentRestriction n k hVU T) := rfl

/-- Every genuine maximal Hilbert differential graph pair obeys the actual intrinsic current
differential equation on every quotient set of supported compact tests. -/
theorem intrinsicHilbertCurrent_differential (n k : ℕ) (U : Set OrbitSpace)
    (u : Hilbert n k) (z : Hilbert n (k+1))
    (h : (u,z) ∈ (maximalDifferential n k).graph) :
    intrinsicCurrentDifferential n k U (intrinsicHilbertCurrent n k U u) =
      intrinsicHilbertCurrent n (k+1) U z := by
  apply LinearMap.ext
  intro w
  exact (congrArg (fun T : TestDual n (k+1) => T w.val)
    ((maximal_graph_iff_testDifferential n k u z).mp h))

end TernaryPoly.PolynomialFormWeakSmooth
