module

public import TernaryPeriodPolynomials.DifferentialForm.WeakTests
public import TernaryPeriodPolynomials.DifferentialForm.WeakSmooth.ClosednessAlgebra

@[expose] public section


/-! Smooth closedness follows from the actual maximal weak derivative equation. -/
noncomputable section
namespace TernaryPoly.PolynomialFormWeakSmooth
open PolynomialCoefficientMetric PolynomialFormCoordinates PolynomialFormHilbert
open SmoothCoveringDeRham

/-- A compact smooth form with an actual weak primitive is smoothly closed. -/
theorem compactDifferential_eq_zero_of_weak_primitive (n k : ℕ)
    (ω : Core n (k + 1)) (u : Hilbert n k)
    (hu : (u, inclusion n (k + 1) ω) ∈ (maximalDifferential n k).graph) :
    compactDifferential (deckRepresentation n) isOpen_univ (k + 1) ω = 0 :=
  derivative_eq_zero_of_weak_primitive
    (inclusion n k) (inclusion n (k + 1)) (inclusion n (k + 1 + 1))
    (inclusion_injective n (k + 1 + 1))
    (compactDifferential (deckRepresentation n) isOpen_univ (k + 1))
    (compactAdjoint n k) (compactAdjoint n (k + 1))
    (inner_compactDifferential_compactAdjoint n (k + 1))
    (compactAdjoint_squared n k) ω u
    ((mem_maximalDifferential_graph_iff n k u (inclusion n (k + 1) ω)).mp hu)

/-- The conclusion is the literal exterior derivative of the underlying smooth form. -/
theorem differential_eq_zero_of_weak_primitive (n k : ℕ)
    (ω : Core n (k + 1)) (u : Hilbert n k)
    (hu : (u, inclusion n (k + 1) ω) ∈ (maximalDifferential n k).graph) :
    SmoothCoveringDeRham.differential (deckRepresentation n) isOpen_univ (k + 1) ω.val = 0 :=
  congrArg Subtype.val (compactDifferential_eq_zero_of_weak_primitive n k ω u hu)

end TernaryPoly.PolynomialFormWeakSmooth
