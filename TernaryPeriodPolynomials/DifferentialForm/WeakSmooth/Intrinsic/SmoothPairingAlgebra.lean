module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothPairing

@[expose] public section


/-! True bilinearity of the intrinsic quotient metric pairing. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialCoefficientMetric PolynomialFormMetric SymmetricSpaceCovering SmoothCoveringDeRham

/-- Additivity in the genuine smooth local form. -/
theorem intrinsicSmoothPairing_add_left (n k : ℕ) (U : Set OrbitSpace)
    (a b : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) :
    intrinsicSmoothPairing n k U (a+b) w = intrinsicSmoothPairing n k U a w + intrinsicSmoothPairing n k U b w :=
  scalarPairing_add_left n k a b (supportedLocalTest n k U w).val

/-- Scalar linearity in the genuine smooth local form. -/
theorem intrinsicSmoothPairing_smul_left (n k : ℕ) (U : Set OrbitSpace) (c : ℝ)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) :
    intrinsicSmoothPairing n k U (c • a) w = c • intrinsicSmoothPairing n k U a w :=
  scalarPairing_smul_left n k c a (supportedLocalTest n k U w).val

/-- Additivity in the actual intrinsic compact quotient test. -/
theorem intrinsicSmoothPairing_add_right (n k : ℕ) (U : Set OrbitSpace)
    (a : EquivariantForm (deckRepresentation n) U k) (w z : supportedCompactCore n k U) :
    intrinsicSmoothPairing n k U a (w+z) = intrinsicSmoothPairing n k U a w + intrinsicSmoothPairing n k U a z :=
  (congrArg (fun t : CompactSupportForm (deckRepresentation n) U k => scalarPairing n k a t.val)
    (map_add (supportedLocalTest n k U) w z)).trans
      (scalarPairing_add_right n k a (supportedLocalTest n k U w).val (supportedLocalTest n k U z).val)

/-- Scalar linearity in the actual intrinsic compact quotient test. -/
theorem intrinsicSmoothPairing_smul_right (n k : ℕ) (U : Set OrbitSpace) (c : ℝ)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U) :
    intrinsicSmoothPairing n k U a (c • w) = c • intrinsicSmoothPairing n k U a w :=
  (congrArg (fun t : CompactSupportForm (deckRepresentation n) U k => scalarPairing n k a t.val)
    (map_smul (supportedLocalTest n k U) c w)).trans
      (scalarPairing_smul_right n k c a (supportedLocalTest n k U w).val)

/-- The actual local smooth quotient metric pairing is bilinear in its genuine two inputs. -/
def intrinsicSmoothPairingLinear (n k : ℕ) (U : Set OrbitSpace) :
    EquivariantForm (deckRepresentation n) U k →ₗ[ℝ]
      supportedCompactCore n k U →ₗ[ℝ] (OrbitSpace → ℝ) where
  toFun a :=
    { toFun w := intrinsicSmoothPairing n k U a w
      map_add' := intrinsicSmoothPairing_add_right n k U a
      map_smul' := fun c w => intrinsicSmoothPairing_smul_right n k U c a w }
  map_add' a b := LinearMap.ext (intrinsicSmoothPairing_add_left n k U a b)
  map_smul' c a := LinearMap.ext (intrinsicSmoothPairing_smul_left n k U c a)

end TernaryPoly.PolynomialFormWeakSmooth
