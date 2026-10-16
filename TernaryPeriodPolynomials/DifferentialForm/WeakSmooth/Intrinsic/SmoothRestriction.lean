module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.SmoothCurrent

@[expose] public section


/-! Genuine restriction compatibility of actual local smooth quotient currents. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set MeasureTheory PolynomialCoefficientMetric PolynomialCoefficientBundle PolynomialFormMetric
  SymmetricSpaceCharts SymmetricSpaceCovering SmoothCoveringDeRham SmoothLocalDeRham

/-- The actual intrinsic smooth pairing at a positive coordinate uses the literal raw local
form and the literal raw supported global compact test. -/
theorem intrinsicSmoothPairing_coordinateProjection (n k : ℕ) (U : Set OrbitSpace)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k U)
    (x : Coordinates) (hx : x ∈ positiveCoordinates) :
    intrinsicSmoothPairing n k U a w (coordinateProjection x) =
      formPairing n k x (a.val.val x) (w.val.val.val.val x) :=
  (scalarPairing_coordinateProjection n k a (supportedLocalTest n k U w).val x hx).trans
    (congrArg (formPairing n k x (a.val.val x)) (congrFun (supportedCompactCore_restrict_raw n k U w) x))

/-- Genuine local smooth quotient pairings restrict naturally against actual supported tests. -/
theorem intrinsicSmoothPairing_restriction (n k : ℕ) {U V : Set OrbitSpace} (hVU : V ⊆ U)
    (a : EquivariantForm (deckRepresentation n) U k) (w : supportedCompactCore n k V) :
    intrinsicSmoothPairing n k V (restrictEquivariant (deckRepresentation n) hVU k a) w =
      intrinsicSmoothPairing n k U a (supportedCompactInclusion n k hVU w) := by
  funext q
  let x := coordinateChart (chosenLift q)
  have hproj : coordinateProjection x = q := by
    simp only [x, coordinateProjection, coordinateChart.left_inv (by simp), chosenLift_projection]
  have hpos : x ∈ positiveCoordinates := extract_mem _
  apply (congrArg (intrinsicSmoothPairing n k V (restrictEquivariant (deckRepresentation n) hVU k a) w) hproj).symm.trans
  apply (intrinsicSmoothPairing_coordinateProjection n k V _ w x hpos).trans
  apply Eq.trans _ ((intrinsicSmoothPairing_coordinateProjection n k U a
    (supportedCompactInclusion n k hVU w) x hpos).symm.trans
      (congrArg (intrinsicSmoothPairing n k U a (supportedCompactInclusion n k hVU w)) hproj))
  by_cases hx : x ∈ liftedDomain V
  · exact congrArg (fun z => formPairing n k x z (w.val.val.val.val x))
      (restrictEquivariant_apply (deckRepresentation n) hVU a hx)
  · have hz := supportedCompactCore_outside_lifted n k V w hx
    change formPairing n k x _ (w.val.val.val.val x) = formPairing n k x _ (w.val.val.val.val x)
    simp only [hz, formPairing_zero_right]

/-- The genuine smooth-current embedding is compatible with intrinsic restriction on actual
quotient open sets, independently of choices of local charts. -/
theorem intrinsicSmoothCurrent_restriction (n k : ℕ) {U V : Set OrbitSpace}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U)
    (a : EquivariantForm (deckRepresentation n) U k) :
    intrinsicCurrentRestriction n k hVU (intrinsicSmoothCurrent n k U hU a) =
      intrinsicSmoothCurrent n k V hV (restrictEquivariant (deckRepresentation n) hVU k a) := by
  apply LinearMap.ext
  intro w
  change (∫ q, intrinsicSmoothPairing n k U a (supportedCompactInclusion n k hVU w) q ∂SymmetricSpaceRiemannian.orbitVolume) = _
  exact congrArg (fun f : OrbitSpace → ℝ => ∫ q, f q ∂SymmetricSpaceRiemannian.orbitVolume)
    (intrinsicSmoothPairing_restriction n k hVU a w).symm

end TernaryPoly.PolynomialFormWeakSmooth
