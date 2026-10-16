module

public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.Intrinsic.Tests
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingExtension

@[expose] public section


/-! Actual supported global compact forms are genuine compact tests on the corresponding quotient open. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open Set PolynomialCoefficientMetric PolynomialFormHilbert SymmetricSpaceCharts SymmetricSpaceCovering
  SmoothLocalDeRham SmoothCoveringDeRham

/-- A genuine supported compact test vanishes outside the actual lifted local domain. -/
theorem supportedCompactCore_outside_lifted (n k : ℕ) (U : Set OrbitSpace)
    (w : supportedCompactCore n k U) {x : Coordinates} (hx : x ∉ liftedDomain U) :
    w.val.val.val.val x = 0 := by
  by_contra hw
  have hpos : x ∈ positiveCoordinates := by
    by_contra hp
    exact hw (Form.outside w.val.val.val (fun h => hp h.1))
  exact hx ⟨hpos, w.property (subset_closure ⟨x, hw, rfl⟩)⟩

/-- Restricting an actual supported global compact test to its local quotient domain keeps its
literal canonical raw representative unchanged everywhere. -/
theorem supportedCompactCore_restrict_raw (n k : ℕ) (U : Set OrbitSpace)
    (w : supportedCompactCore n k U) :
    (restrictEquivariant (deckRepresentation n) (subset_univ U) k w.val.val).val.val =
      w.val.val.val.val := by
  funext x
  by_cases hx : x ∈ liftedDomain U
  · exact restrictEquivariant_apply (deckRepresentation n) (subset_univ U) w.val.val hx
  · exact (Form.outside _ hx).trans (supportedCompactCore_outside_lifted n k U w hx).symm

/-- The genuine quotient support is unchanged under restriction of an actual supported test. -/
theorem supportedCompactCore_restrict_support (n k : ℕ) (U : Set OrbitSpace)
    (w : supportedCompactCore n k U) :
    quotientSupport (restrictEquivariant (deckRepresentation n) (subset_univ U) k w.val.val) =
      quotientSupport w.val.val :=
  congrArg (fun f : RawForm Coordinates (Coefficients n) k => closure (coordinateProjection '' Function.support f))
    (supportedCompactCore_restrict_raw n k U w)

/-- Actual supported-test restriction satisfies the genuine local compact-support condition. -/
theorem supportedLocalTest_compact (n k : ℕ) (U : Set OrbitSpace)
    (w : supportedCompactCore n k U) :
    HasQuotientCompactSupport (deckRepresentation n)
      (restrictEquivariant (deckRepresentation n) (subset_univ U) k w.val.val) := by
  change IsCompact (quotientSupport _) ∧ quotientSupport _ ⊆ U
  exact (supportedCompactCore_restrict_support n k U w).symm ▸ ⟨w.val.property.1, w.property⟩

/-- Every actual global compact test supported over U is an actual quotient-compact local test on U. -/
def supportedLocalTest (n k : ℕ) (U : Set OrbitSpace) :
    supportedCompactCore n k U →ₗ[ℝ] CompactSupportForm (deckRepresentation n) U k where
  toFun w := ⟨restrictEquivariant (deckRepresentation n) (subset_univ U) k w.val.val,
    supportedLocalTest_compact n k U w⟩
  map_add' w z := Subtype.ext (map_add (restrictEquivariant (deckRepresentation n) (subset_univ U) k) w.val.val z.val.val)
  map_smul' c w := Subtype.ext (map_smul (restrictEquivariant (deckRepresentation n) (subset_univ U) k) c w.val.val)

end TernaryPoly.PolynomialFormWeakSmooth
